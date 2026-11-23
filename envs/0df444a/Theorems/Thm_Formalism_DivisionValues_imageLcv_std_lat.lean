-- Prove2me | Theorems.Thm_Formalism_DivisionValues_imageLcv_std_lat
-- name    : Formalism.DivisionValues.imageLcv_std_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:01.548688+00:00
-- url     : https://prove2.me/theorems/01375842-ad82-4677-ae1d-45bab622d65c
-- title:
--   Division Values: image Lcv std lat
-- statement:
--   The Division Values construction uses the image Lcv std lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean#L121-L126

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.DivisionValues.imageLcv_std_lat (d : ℕ) :
    Submodule.IsLattice K
      (Submodule.span (𝓞 K) (Set.range (fun i => (Pi.single i 1 : Fin d → K)))) := by sorry
