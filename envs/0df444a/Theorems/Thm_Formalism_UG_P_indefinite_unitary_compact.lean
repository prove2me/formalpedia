-- Prove2me | Theorems.Thm_Formalism_UG_P_indefinite_unitary_compact
-- name    : Formalism.UG.P.indefinite_unitary_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:37.95408+00:00
-- url     : https://prove2.me/theorems/af1aa797-ea14-47b7-9900-4c4a1fb5d432
-- title:
--   P: indefinite unitary compact
-- statement:
--   The P construction uses the indefinite unitary compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Upqcpt.lean#L83-L90

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Upqcpt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.indefinite_unitary_compact : Formalism.UG.UpqCompact := by sorry
