-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_anti
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_anti
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:43.462874+00:00
-- url     : https://prove2.me/theorems/87fe7375-ebe9-43ee-a2f7-c4ab3cc2acb1
-- title:
--   Pgsn2pfran: ind anti
-- statement:
--   The Pgsn2pfran construction uses the ind anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_LayerCakeFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Finset MeasureTheory
open Formalism.CorankShareLayerCake.FR.Pgsn2pfran

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_anti (c : ℝ) : Antitone (fun τ : ℝ => if τ < c then (1:ℝ) else 0) := by sorry
