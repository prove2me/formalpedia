-- Prove2me | Theorems.Thm_Formalism_mellinElem_part1
-- name    : Formalism.mellinElem_part1
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:10.842956+00:00
-- url     : https://prove2.me/theorems/c0f5ab7c-f169-4366-8c29-3543a0d2e11b
-- title:
--   Formalism: mellin Elem part1
-- statement:
--   The Formalism construction uses the mellin Elem part1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinElem.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MellinElem.lean#L9-L16

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism

theorem Formalism.mellinElem_part1 (a σ : ℝ) (h : a < σ) :
    IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1) := by sorry
