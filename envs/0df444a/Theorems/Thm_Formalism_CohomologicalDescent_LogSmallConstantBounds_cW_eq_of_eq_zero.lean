-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_cW_eq_of_eq_zero
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.cW_eq_of_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:44:59.053093+00:00
-- url     : https://prove2.me/theorems/2ef90200-0090-484b-b229-c34b98536002
-- title:
--   Log Small Constant Bounds: c W eq of eq zero
-- statement:
--   The Log Small Constant Bounds construction uses the c W eq of eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L778-L785
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L778-L785

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.cW_eq_of_eq_zero {ι : Type} (D : SizeData₂ ι) (P : Par) (τ : ι) (l : ℕ) (h1 : D.mw τ l = 0)
    (h2 : D.mwF τ l = 0) (h3 : D.ecl τ l = 0) :
    D.cW P τ l = ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((P.h + (P.Nr : ℝ)) / ((l : ℝ) - 1) + 6)
      + (P.k : ℝ) * (P.S / (l : ℝ) + IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ))
      + gatedCoefficientTerm D P τ l
      + ((D.q τ : ℝ) * P.h / (l : ℝ)) * (1 + max 0 (Real.log (P.h / (l : ℝ)))) := by sorry
