-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_correction_weight_eq_formula
-- name    : Formalism.CohomologicalDescent.ShortWeightBounds.correction_weight_eq_formula
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:18.023938+00:00
-- url     : https://prove2.me/theorems/47b93019-589c-45e4-be4f-1325257023b6
-- title:
--   Short Weight Bounds: correction weight eq formula
-- statement:
--   The Short Weight Bounds construction uses the correction weight eq formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L498-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WeightBounds.lean#L498-L506

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds

theorem Formalism.CohomologicalDescent.ShortWeightBounds.correction_weight_eq_formula {ι : Type} (W : Wts ι) (P : Par) (J : ℕ → ℕ) (τ : ι) (l : ℕ) :
    (W.sizeData₂ P J).cW P τ l =
      ((W.q τ : ℝ) + 2 * (W.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
        + (W.ecl P τ l : ℝ)
        + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (W.xm τ) (W.xp τ) (W.top P τ))
        + (if ((d0 l (W.xm τ - W.top P τ) : ℕ) : ℤ) < W.xm τ - W.top P τ then
            min (min (P.k : ℝ) (P.t : ℝ))
              ((W.sizeData₂ P J).depth P τ l / (d0 l (W.xm τ - W.top P τ) : ℝ)) else 0)
        + ((W.sizeData₂ P J).depth P τ l / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by sorry
