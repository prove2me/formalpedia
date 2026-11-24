-- Prove2me | Theorems.Thm_Formalism_L2_NCov_commute_sub_smul
-- name    : Formalism.L2.NCov.commute_sub_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:27.138042+00:00
-- url     : https://prove2.me/theorems/edf9939c-16d9-4e9f-a3c9-3270174abe01
-- title:
--   NCov: commute sub smul
-- statement:
--   The NCov construction uses the commute sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L28-L31

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.NCov.commute_sub_smul {A B : End K V} (h : Commute A B) (a b : K) :
    Commute (A - a • 1) (B - b • 1) := by sorry
