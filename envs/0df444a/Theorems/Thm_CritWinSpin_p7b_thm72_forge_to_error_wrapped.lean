-- Prove2me | Theorems.Thm_CritWinSpin_p7b_thm72_forge_to_error_wrapped
-- name    : CritWinSpin.p7b_thm72_forge_to_error_wrapped
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:31.838234+00:00
-- url     : https://prove2.me/theorems/9b11bf7d-16a2-4a71-a73e-eda96b6ed486
-- title:
--   Theorem 7.2 (eq. 40), corrected wrapper-forgery core
-- statement:
--   Let $A$ be a polynomial-time learner for either sample extension or sample amplification. There is a polynomial-time wrapper $B$, constructed from $A$ by simulating $\hat L_{T,k}$, running $A$ on the lifted instance, and returning the first valid configuration with a fresh message, such that for all sufficiently large $d$,
--   $$
--   1-\operatorname{forgeProb}(B,T,d)-\left(T+\binom T2\right)2^{-d}-2Te^{-n_0^2}-v_1(d)-v_2(d)
--   \le E_{\mathrm{task}}(A;k),
--   $$
--   where $\mathrm{task}$ is extension or amplification. The extension and amplification wrappers may differ.
--
--   This is the forgery-probability form of Theorem 7.2, eq. (40). Applying `SourceProps`(iii) to each wrapper subsequently replaces its forgery probability by $C\,T\sqrt d\,\operatorname{Adv}_{\mathrm{CDH}}$.
--
--   **Formalization Note.** The quantified forger $B$ is essential: the proof constructs $B$ from the learner $A$, and does not assert that the learner itself has a large source-forging probability. This corrects the identifier collision in `p7b_thm72_forge_to_error`, where the same `A` was used for both roles.
-- source:
--   Liu, Zhang, Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission (manuscript sha256 f77584da…), pp.27–28, Theorem 7.2 proof, eq. (40): the wrapper runs \hat L_{T,k} and A and returns the fresh configuration F_*.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false

theorem CritWinSpin.p7b_thm72_forge_to_error_wrapped (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
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
      1 - forgeProb src B (T d) d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExt S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - forgeProb src B (T d) d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmp S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) := by sorry
