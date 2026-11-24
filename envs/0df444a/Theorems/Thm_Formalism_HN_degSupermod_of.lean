-- Prove2me | Theorems.Thm_Formalism_HN_degSupermod_of
-- name    : Formalism.HN.degSupermod_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:04.857798+00:00
-- url     : https://prove2.me/theorems/89e0520d-882a-4f20-8cb4-e5495b0d51da
-- title:
--   HN: deg Supermod of
-- statement:
--   The HN construction uses the deg Supermod of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermod.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/DegSupermod.lean#L44-L50

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
universe u v w in

theorem Formalism.HN.degSupermod_of (h : DegSupermodZ.{w}) : DegSupermod.{u, v, w} := by sorry
