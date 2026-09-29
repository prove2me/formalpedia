-- Prove2me | solution 1 for mme_stothers_phi116_outer_hashing_value_of_support_and_components
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-07T03:15:46.237722+00:00
-- url     : https://prove2.me/submissions/1d4d400e-86dd-49b3-8da5-45e7f2a3d665

import Theorems.Thm_mme_stothers_phi116_outer_hashing_value

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (tau : Real)
    (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (hsupport :
      ∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        (MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockTensor sigma = 0)
    (hcomponents :
      TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 1, 2]) ∧
        TensorObj.Restrict (MMObj K 12 1 12)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 0, 2]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![0, 0, 0]) ∧
        TensorObj.Restrict (coupledObj K 6)
          ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
            ![1, 1, 1])) :
    ∀ V : Real, 0 ≤ V →
      V < MME.StothersFourth.classValue 6 tau 5 →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (MME.StothersFourth.cwFourthConstituent K 6 1 1 6)) tau V := by
  exact
    mme_stothers_phi116_outer_hashing_value
      tau htauLower htauUpper hsupport hcomponents
