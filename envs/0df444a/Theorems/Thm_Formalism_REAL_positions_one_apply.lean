-- Prove2me | Theorems.Thm_Formalism_REAL_positions_one_apply
-- name    : Formalism.REAL.positions_one_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:24:14.629639+00:00
-- url     : https://prove2.me/theorems/a24fdb4d-b5fc-41bd-b02f-4e3f3fff42f5
-- title:
--   REAL: positions one apply
-- statement:
--   The REAL construction uses the positions one apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L326-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L326-L330

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.positions_one_apply (c d : Fin n) (G : Arr V n 1) (a b : Fin n) :
    positionsE V n 1 c d G (fun _ => (a, b)) =
      (if a = c then G (fun _ => (d, b)) else 0) - (if b = d then G (fun _ => (a, c)) else 0) := by sorry
