-- Prove2me | Theorems.Thm_CritWinSpin_theorem_7_2
-- name    : CritWinSpin.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:11.674401+00:00
-- url     : https://prove2.me/theorems/3d930509-72a1-4867-938c-b24518a1b454
-- title:
--   Theorem 7.2, p.27 — $E_{\mathrm{task}}(A;k)\ge1-O(T\sqrt d)\mathrm{Adv}_{\mathrm{CDH}}(B)-\dots$, eq. (40)
-- statement:
--   Let $(H,\mu_H,\Omega,V,\Psi)$ be a source as in Theorem 5.1 with constant $C$ in (27), $M=(\tilde J,\tilde h)$ and $\hat L_{T,k}$ as in Theorem 6.3, and $\mathrm{TV}(\hat L_{T,k}(\mu_H^{\otimes T}),\pi_M^{\otimes k})\le v_{T,k}$. For any PPT $A$, any polynomial $k,T$ with $T\ge\lceil C_{\mathrm{cap}}(k+1+n^2)\rceil$, and $E_{\mathrm{task}}\in\{E_{\mathrm{ext}},E_{\mathrm{amp}}\}$, there is a PPT $B$ such that for all large $d$
--   $$E_{\mathrm{task}}(A;k)\ge1-CT\sqrt d\,\mathrm{Adv}_{\mathrm{CDH}}(B)-\Bigl(T+\binom T2\Bigr)2^{-d}-2Te^{-n_0^2}-v_{T,k}-v_{T,k+1},$$
--   with $M$ drawn by KeyGen and the lift.
--
--   Together with CDH and Theorem 6.3 this yields clause (ii) of the main theorem.
--
--   Differences from the source:
--   - generalization: (H, µ_H, Ω, V, Ψ) one of the two sources of Theorem 5.1 → any source with SourceProps and constant C; reason: the proof uses only those properties; both sources of Theorem 5.1 satisfy them
--   - reading: k = poly(d), T = poly(d) → k, T polynomially bounded and computable in polynomial time (EffPoly); reason: the uniform B runs L̂_{T,k}, so it needs k and T
--   - generalization: M and L̂_{T,k} as in Theorem 6.3, with T ≥ ⌈C_cap(k + 1 + n²)⌉ for the C_cap of Theorem 6.3 → explicit hypotheses for all large d: a polynomial-time lift map, û with (28), any PPT slot machine with the decoding clause, and any constant C_cap > 0; reason: those are the properties of Theorem 6.3 that the proof uses; C_cap only serves to make v_{T,k}, v_{T,k+1} small, and these are hypotheses here; the objects of Theorem 6.3 satisfy all of them
--   - encoding: O(T√d) → the constant C of (27) and an eventual bound; reason: (27) is applied to one wrapper of A; the paper's O is asymptotic in d
--   - encoding: TV(L̂_{T,k}(µ_H^{⊗T}), π_M^{⊗k}) ≤ v_{T,k} → v₁(d), v₂(d) bounding that TV at every key in the support of KeyGen(1^d), d ≥ d₁; reason: M is a function of P, and the bound is used at each P
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), Theorem 7.2, p.27, eq. (40); §7, p.26

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

namespace CritWinSpin

/-- **Theorem 7.2** (Liu–Zhang–Ren, STOC 2027 submission, manuscript sha256 f77584da…, p.27). Let
`(H, μ_H, Ω, V, Ψ)` be a source with `SourceProps` and constant `C`, and let `M = (J̃, h̃)` and the slot machine
of `L̂_{T,k}` be as in Theorem 6.3 at every key for large `d`, with
`TV(L̂_{T,k}(μ_H^{⊗T}), π_M^{⊗k}) ≤ v_{T,k}`. For every PPT `A` and polynomial `k`, `T` with
`T ≥ ⌈C_cap(k + 1 + n²)⌉`, and `E_task ∈ {E_ext, E_amp}`, there is a PPT `B` with
`E_task(A; k) ≥ 1 − C T √d Adv_CDH(B) − (T + (T choose 2)) 2^{−d} − 2T e^{−n₀²} − v_{T,k} − v_{T,k+1}`,
eq. (40), for all large `d`. `M` is drawn by `KeyGen`, then the lift.

**Formalization Note.** `k` and `T` are efficiently computable because the uniform algorithm `B` runs
`L̂_{T,k}`. The theorem applies to both sources of Theorem 5.1 at once: `src` is any source with `SourceProps`. -/
theorem theorem_7_2 (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (F : BilinearFamily) (src : BinarySource F) (C : ℝ) (hC : 0 < C) (hsrc : SourceProps F src C)
    (w ε : ℝ) (Ac Cc : ℕ) (hw : 1 ≤ w) (hε : 0 < ε) (hεd : ε < dExp p)
    (hpar : GadgetParams p w ε Ac Cc)
    (Ccap : ℝ) (hCcap : 0 < Ccap)
    (liftF : Str → Str) (hliftF : CookPvsNP.PolyTimeComputable liftF) (slotM : PPT)
    (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ)
    (hlift : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) (û d desc key) ∧
      liftF (encInst (src.ham d desc key)) =
        tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
          encRat (û d desc key)])
    (hdec : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key)))
    (k T : ℕ → ℕ) (hk : EffPoly k) (hk₁ : ∀ d, 1 ≤ k d) (hT : EffPoly T)
    (hTk : ∀ d, ⌈Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d)
    (v₁ v₂ : ℕ → ℝ)
    (hv₁ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d)) ≤ v₁ d)
    (hv₂ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d + 1))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d + 1)) ≤ v₂ d)
    (A : PPT) :
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExt S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmp S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) := by sorry

end CritWinSpin
