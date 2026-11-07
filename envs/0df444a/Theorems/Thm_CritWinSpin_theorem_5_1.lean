-- Prove2me | Theorems.Thm_CritWinSpin_theorem_5_1
-- name    : CritWinSpin.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:42:15.569489+00:00
-- url     : https://prove2.me/theorems/571141a0-e49a-440c-9c08-e38d113424da
-- title:
--   Theorem 5.1, p.19 — the binary Ising source from Waters signatures and its zero-field version
-- statement:
--   For every bilinear family there is a verification circuit on $n_0=\mathrm{poly}(d)$ wires, $n_0\ge d^2$, whose evaluation on valid message–signature triples is polynomial-time and has the message as its message bits, and an explicitly computable zero-diagonal Ising model $H_P$ on $\{\pm1\}^{n_0}$ with $\mathrm{wd}(J_0,h_0)\le n_0^{w_0}$ and Gibbs law $\mu_P$, such that:
--
--   1. $\mathrm{TV}(\mu_P,V_P)\le e^{-n_0^2}$ and $\mathrm{TV}(V_P^{\otimes T},\mu_P^{\otimes T})\le Te^{-n_0^2}$ for all $T\ge1$;
--   2. sampling $m\sim\mathrm{Unif}(\{0,1\}^d)$, signing and evaluating $C_{\mathrm{ver}}$ generates $F\sim V_P$ with $\Psi_P(F)$ uniform; for $F_{1:T}\sim V_P^{\otimes T}$, any predictor of $\Psi_P(F_i)$ from $(P,F_{-i})$ succeeds with probability $2^{-d}$, and the messages fail to be distinct with probability at most $\binom T22^{-d}$;
--   3. for every PPT $A$ there is a PPT $B$ with
--   $$\mathbb P\{A(P,F_{1:T})=F^*\in\Omega_P,\ \Psi_P(F^*)\notin\{\Psi_P(F_t)\}_t\}\le C\,T\sqrt d\,\mathrm{Adv}_{\mathrm{CDH}}(B).$$
--
--   Moreover the zero-field model $\hat H_P$ on $n=n_0+1$ spins has zero diagonal, zero field and width at most $n^w$, and satisfies the same three items with $(\mu_{\hat H_P},\hat\Omega_P,\hat V_P,\hat\Psi_P)$; drawing $F\sim V_P$ and an independent sign $t$ generates $(t,tF)\sim\hat V_P$.
--
--   Item 3 is a reduction, so no CDH hypothesis appears. This is the cryptographic source of the lower bound.
--
--   Differences from the source:
--   - reading: G(1^d) = (G, G_T, q_g, g, e) with group operations → the exponent representation BilinearFamily: injective codes and polynomial-time maps; reason: every prime-order pairing group has this form via a ↦ g^a; see that definition
--   - reading: a Boolean circuit of NAND gates C_ver on n₀ = poly(d) wires (n₀ ≥ d²), with Ω_P its evaluations on valid pairs → ∃ polynomially bounded n₀ ≥ d² and a polynomial-time evaluation on valid triples, with Ω_P its image; reason: the paper does not give the circuit and uses only these properties
--   - reading: (27) with O(T√d) for any PPT A → ∃ C > 0 before F, A and T; for every efficiently computable polynomial T ≥ 1, ∃ B, for all large d: forgeProb ≤ C T √d Adv(B); reason: the constant of [HJK12, Theorem 2.3] is universal; B is uniform and has to simulate T samples, so T must be computable; the equality in (27) is an upper bound
--   - reading: any predictor 𝒫 → a stochastic kernel from F_{−i} to messages, at fixed P; reason: Lemma 7.1 applies it to a randomized predictor
--   - encoding: the model is explicitly computable from P → a polynomial-time map from the public-key string to the code of (J₀, h₀), and likewise for Ψ_P; reason: the meaning of explicitly computable, needed by the reduction
--   - reading: satisfies (i)–(iii) with hats in place, including Sign and evaluating C_ver in (ii) → for the hat source, generation is: draw F ∼ V_P and an independent t, output (t, tF) ∼ V̂_P; reason: the paper's own proof on p.20; the zero-field source has no separate signing
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 5.1, p.19, eqs. (26), (27); §5.1, p.18; §5.2, pp.18–19

import Mathlib
import Definitions.Def_CritWinSpin_BinarySource
open QAlgorithms.Complexity QuantumPRC
set_option autoImplicit false

namespace CritWinSpin

/-- **Theorem 5.1, binary Ising source** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…,
p.19). For every bilinear family there is a verification circuit on `n₀ = poly(d) ≥ d²` wires, evaluated in
polynomial time, whose message bits on a valid triple are the message, whose Waters generation has law `V_P`,
and whose source `(H_P, Ω_P, Ψ_P)` and zero-field source `(Ĥ_P, Ω̂_P, Ψ̂_P)` of (26) satisfy (i)–(iii)
(`SourceProps`), with one universal constant `C` in (27). Drawing `F ∼ V_P` and an independent sign `t`
generates `(t, tF) ∼ V̂_P`. No CDH hypothesis: (iii) is a reduction. -/
theorem theorem_5_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ F : BilinearFamily, ∃ circ : WatersCircuit F,
      PolyBounded circ.n0 ∧ (∀ d, d ^ 2 ≤ circ.n0 d) ∧
      (∃ evalF : Str → Str, CookPvsNP.PolyTimeComputable evalF ∧
        ∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
          (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
          evalF (tupleCode [pkCode F d desc key, List.ofFn m, F.encG desc s₁, F.encG desc s₂]) =
            List.ofFn (circ.evalCfg d desc key m s₁ s₂)) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (m : Fin d → Bool) (s₁ s₂ : ZMod (F.q desc)), IsValidSig key m s₁ s₂ →
        circ.psi d desc key (circ.evalCfg d desc key m s₁ s₂) = m) ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d)), circ.genLaw d desc key y = unifOn (circ.omega d desc key) y) ∧
      SourceProps F circ.toSource C ∧
      SourceProps F (hatSource circ.toSource) C ∧
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d + 1)),
        (1 / 2 : ℝ) * ∑ t : Bool, ∑ Y : BinCfg (circ.n0 d), unifOn (circ.omega d desc key) Y *
            (if (Fin.cons t (fun i => t == Y i) : BinCfg (circ.n0 d + 1)) = y then (1 : ℝ) else 0) =
          unifOn ((hatSource circ.toSource).omega d desc key) y) := by sorry

end CritWinSpin
