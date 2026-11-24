-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_toNat_xlo_sub_maxB_bounds
-- name    : Formalism.CohomologicalDescent.LogSmallConstantBounds.toNat_xlo_sub_maxB_bounds
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:37.770553+00:00
-- url     : https://prove2.me/theorems/e7b28bed-9294-4fa5-b847-16ad68a3720d
-- title:
--   Log Small Constant Bounds: to Nat xlo sub max B bounds
-- statement:
--   The Log Small Constant Bounds construction uses the to Nat xlo sub max B bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L900-L906
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/ParameterBounds.lean#L900-L906

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

theorem Formalism.CohomologicalDescent.LogSmallConstantBounds.toNat_xlo_sub_maxB_bounds {P : Par} (H : P.Hyp) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) :
    (((D.xlo τ - D.maxB τ).toNat : ℕ) : ℤ) = D.xlo τ - D.maxB τ ∧
      1 ≤ (D.xlo τ - D.maxB τ).toNat ∧ (D.xlo τ - D.maxB τ).toNat ≤ ⌊P.h⌋₊ := by sorry
