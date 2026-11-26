-- Prove2me | solution 1 for norm_aeval_le_polynomialSupNorm_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:47.304656+00:00
-- url     : https://prove2.me/submissions/80896332-37a3-418c-b62b-9b30fb913b36

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_SpectralSet_Normal
import Theorems.Thm_norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval

set_option autoImplicit false
open Polynomial
theorem _root_.solution {A : Type*} [CStarAlgebra A]
    (a : A) [IsStarNormal a] {K : Set ℂ} (hK : IsCompact K) (hσ : spectrum ℂ a ⊆ K)
    (p : ℂ[X]) : ‖aeval a p‖ ≤ polynomialSupNorm p K := by
  have hnormal : IsStarNormal (aeval a p) := by
    rw [← cfc_polynomial p a]
    exact cfc_predicate _ a
  let _ := hnormal
  exact norm_aeval_le_polynomialSupNorm_of_isStarNormal_aeval a hK hσ p
