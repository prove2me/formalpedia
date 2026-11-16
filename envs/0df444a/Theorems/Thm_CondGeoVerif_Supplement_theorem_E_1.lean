-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_E_1
-- name    : CondGeoVerif.Supplement.theorem_E_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:16:45.394342+00:00
-- url     : https://prove2.me/theorems/bb6fe476-a78f-48ac-b87b-649a520eb01c
-- title:
--   Theorem E.1 — globally sound high-signal verification of homogeneous halfspaces with $m_V=O_{a_0}(\varepsilon^{-1}\log(e/(\varepsilon\delta)))$
-- statement:
--   Let $X\sim N(0,I_d)$, $\mathcal H_d=\{x\mapsto\mathrm{sign}\langle v,x\rangle:v\in S^{d-1}\}$, $R(h)=P(h(X)\ne Y)$, $\mathrm{OPT}=\inf_{h\in\mathcal H_d}R(h)$, $A=\sqrt{2\log2}$ and $a_c=2\Phi(A)-1$. Fix $0<\varepsilon,\delta<1$ and $a_0\in(a_c,1)$. There is a one-message proper verifier using
--   $$m_V=O_{a_0}\Big(\frac1\varepsilon\log\frac e{\varepsilon\delta}\Big)$$
--   private labeled samples such that:
--
--   1. for every labeling distribution with marginal $N(0,I_d)$ and every prover, its probability of outputting a classifier with risk exceeding $\mathrm{OPT}+\varepsilon$ is at most $\delta/2$;
--   2. on every distribution satisfying (E.3), $\mathbb E[Y\mid X]=b(X)h_w(X)$ with $w\in S^{d-1}$ and $b(X)\in[a_0,1]$ almost surely, a sample-only honest prover using $O_{a_0}((d+\log(1/\delta))/\varepsilon^2)$ samples makes it accept, with a correct output, with probability at least $1-\delta$.
--
--   The verifier evaluates one projection and a finite list of scalar band tests. The constants depend only on $a_0$.
--
--   Differences from the source:
--   - reading: the honest prover makes it accept with probability at least 1 − δ → the honest run outputs a predictor with risk ≤ OPT + ε with probability ≥ 1 − δ (OMMassartComplete); reason: Definition 2.1 defines completeness as a correct nonreject output; the stronger of the two readings
--   - encoding: (E.3): E[Y | X] = b(X)h_w(X), b ∈ [a₀, 1] → Massart noise with bound η₀ = (1 − a₀)/2 around h_w ∈ H_d; reason: P(Y ≠ h_w(X) | X) = (1 − b(X))/2; same laws
--   - encoding: O_{a₀}(·) → one constant C chosen after a₀, before d, ε, δ; reason: the subscript names the only dependence
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
--   - reading: the verifier evaluates one projection and a finite list of scalar band tests → the message is a direction v ∈ ℝᵈ, every output is sign⟨v, ·⟩ with ‖v‖ = 1, and the decision depends on the private sample only through ⟨v, Xᵢ⟩ and Yᵢ; reason: the proof (§E.3, p.45) has the prover send only v and the verifier compute the risk and band estimates from T = ⟨v, X⟩ and Y; the band tests are functions of these scalars
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem E.1, pp.43–44 (PDF pp.46–47); model (E.1)–(E.3), p.43

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_critA
import Definitions.Def_CondGeoVerif_Supplement_boolComp

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem E.1 (Globally sound high-signal verification)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, pp.43–44 = PDF pp.46–47).
Fix `0 < ε, δ < 1` and `a₀ ∈ (a_c, 1)`, `a_c = 2Φ(√(2 log 2)) − 1`. There is a one-message proper
verifier for homogeneous halfspaces `H_d` using `m_V = O_{a₀}(ε⁻¹ log(e/(εδ)))` private labeled
samples such that:
1. for every labeling distribution with marginal `N(0, I_d)` and every prover, its probability of
   outputting a classifier with risk exceeding `OPT + ε` is at most `δ/2`;
2. on every distribution satisfying (E.3) (`E[Y | X] = b(X)h_w(X)`, `w ∈ S^{d−1}`,
   `b(X) ∈ [a₀, 1]` a.s.), a sample-only honest prover with `O_{a₀}((d + log(1/δ))/ε²)` samples
   makes it accept with probability at least `1 − δ`.
The verifier evaluates one projection and a finite list of scalar band tests.

**Formalization Note** (E.3) is Massart noise with bound `η₀ = (1 − a₀)/2` around a member of `H_d`
(`P(Y ≠ h_w(X) | X) = (1 − b(X))/2`). Completeness is the published `OMMassartComplete`: the run
accepts *and* outputs a predictor of risk at most `OPT + ε`, with probability `≥ 1 − δ` (Definition
2.1's completeness). The `O_{a₀}` constant `C` is chosen after `a₀` and before `d, ε, δ`.
The message is a proposed direction `v ∈ ℝᵈ` (proof, §E.3: "The prover sends only v"); every output
is the halfspace `x ↦ sign⟨v, x⟩` of a unit message `v`. "Evaluates one projection" is the clause
that the decision depends on the private sample only through the projections `⟨v, Xᵢ⟩` and the
labels `Yᵢ` (the band tests are functions of these scalars). -/
theorem theorem_E_1 (a0 : ℝ) (ha0 : aC < a0) (ha1 : a0 < 1) :
    ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∃ (V : OneMsgVerifier d (Vec d)) (Hon : HonestProver d (Vec d)),
        ProperIn V ({halfRule} : Set (Vec 1 → Bool)) ∧
        (∀ (v : Vec d) (s : Fin V.m → Vec d × Bool) (ω : V.Ω) (h : Vec d → Bool),
          V.decide v s ω = some h → ‖v‖ = 1 ∧ h = fun x => sgn (inner ℝ v x)) ∧
        (∀ (v : Vec d) (s s' : Fin V.m → Vec d × Bool) (ω : V.Ω),
          (∀ i, inner ℝ v (s i).1 = inner ℝ v (s' i).1 ∧ (s i).2 = (s' i).2) →
            V.decide v s ω = V.decide v s' ω) ∧
        OMSound V (halfspaceClass d) ε (δ / 2) ∧
        OMMassartComplete V Hon (halfspaceClass d) ((1 - a0) / 2) ε δ ∧
        (V.m : ℝ) ≤ C * (1 / ε) * Real.log (Real.exp 1 / (ε * δ)) ∧
        (Hon.mP : ℝ) ≤ C * ((d + Real.log (1 / δ)) / ε ^ 2) := by sorry

end CondGeoVerif.Supplement
