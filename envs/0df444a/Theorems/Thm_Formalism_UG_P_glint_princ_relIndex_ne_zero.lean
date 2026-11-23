-- Prove2me | Theorems.Thm_Formalism_UG_P_glint_princ_relIndex_ne_zero
-- name    : Formalism.UG.P.glint_princ_relIndex_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:04.536371+00:00
-- url     : https://prove2.me/theorems/541bef4a-67b0-402a-954c-a5c2a5862cbf
-- title:
--   P: glint princ rel Index ne zero
-- statement:
--   The P construction uses the glint princ rel Index ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L93-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/GlintPrincRelIndexNeZero.lean#L93-L112

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.glint_princ_relIndex_ne_zero (O : Subring L) (I : Ideal O) [Finite (O ⧸ I)] :
    (princ (n := n) O.subtype I).relIndex (bc (n := n) O.subtype).range ≠ 0 := by sorry
