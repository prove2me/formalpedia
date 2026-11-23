-- Prove2me | Theorems.Thm_Formalism_UG_P_rational_points_le_holds
-- name    : Formalism.UG.P.rational_points_le_holds
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:43.407066+00:00
-- url     : https://prove2.me/theorems/f1444534-b17f-45cf-b2f3-e56794cc85d2
-- title:
--   P: rational points le holds
-- statement:
--   The P construction uses the rational points le holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/RationalPointsLeHolds.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/RationalPointsLeHolds.lean#L26-L32

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.rational_points_le_holds : Formalism.UG.RatPtsLe := by sorry
