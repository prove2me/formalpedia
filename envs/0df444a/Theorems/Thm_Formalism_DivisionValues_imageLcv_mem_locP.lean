-- Prove2me | Theorems.Thm_Formalism_DivisionValues_imageLcv_mem_locP
-- name    : Formalism.DivisionValues.imageLcv_mem_locP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:39.363791+00:00
-- url     : https://prove2.me/theorems/f3429b5a-e912-4fcd-bd18-0d3235361a92
-- title:
--   Division Values: image Lcv mem loc P
-- statement:
--   The Division Values construction uses the image Lcv mem loc P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L17-L18

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

theorem Formalism.DivisionValues.imageLcv_mem_locP (p : Ideal R) [p.IsPrime] (A : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := by sorry
