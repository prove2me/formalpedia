-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_dG_val
-- name    : Formalism.UG.P.tjcosets_dG_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:22.479947+00:00
-- url     : https://prove2.me/theorems/45395815-9451-469a-b233-9501a274ecea
-- title:
--   P: tjcosets d G val
-- statement:
--   The P construction uses the tjcosets d G val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsLoc.lean#L105-L106

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
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
open Formalism.UG
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}

theorem Formalism.UG.P.tjcosets_dG_val (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) :
    ((tjcosets_dG n j ϖ hϖ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagJ n ϖ j := by sorry
