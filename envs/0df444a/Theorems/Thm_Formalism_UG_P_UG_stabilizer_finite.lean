-- Prove2me | Theorems.Thm_Formalism_UG_P_UG_stabilizer_finite
-- name    : Formalism.UG.P.UG_stabilizer_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:13:35.346281+00:00
-- url     : https://prove2.me/theorems/864f6f40-4559-48ae-b28a-bcb23e68a3c9
-- title:
--   P: UG stabilizer finite
-- statement:
--   The P construction uses the UG stabilizer finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L215-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L215-L285

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.UG_stabilizer_finite : Formalism.UG.StabFinite := by sorry
