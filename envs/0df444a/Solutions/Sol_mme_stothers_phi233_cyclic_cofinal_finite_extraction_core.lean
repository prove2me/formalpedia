-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_cofinal_finite_extraction_core
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:15:46.64405+00:00
-- url     : https://prove2.me/submissions/82d8a43c-5313-4386-9345-8b7ef8d2142c

import Theorems.Thm_mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : ℝ)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < MME.StothersFourth.classValue 6 tau 9) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization
              (MME.StothersFourth.cwFourthConstituent K 6 2 3 3)).kronPow
                (s n)) ∧
          V ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  exact
    mme_stothers_phi233_cyclic_cofinal_finite_extraction_core_v2
      tau htauLower htauUpper V hV hVlt
