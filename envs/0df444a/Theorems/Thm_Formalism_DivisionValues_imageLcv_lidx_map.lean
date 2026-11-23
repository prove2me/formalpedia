-- Prove2me | Theorems.Thm_Formalism_DivisionValues_imageLcv_lidx_map
-- name    : Formalism.DivisionValues.imageLcv_lidx_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:01.617688+00:00
-- url     : https://prove2.me/theorems/3bbcd0e1-50c0-44c2-93a1-5b41bbbd3b7c
-- title:
--   Division Values: image Lcv lidx map
-- statement:
--   The Division Values construction uses the image Lcv lidx map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L58-L64

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem Formalism.DivisionValues.imageLcv_lidx_map (p : Ideal R) [p.IsPrime] (f : W ≃ₗ[R] W) (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (f : W →ₗ[R] W)) (B.map (f : W →ₗ[R] W)) = Formalism.HermitianLatticesTheory.lidx p A B := by sorry
