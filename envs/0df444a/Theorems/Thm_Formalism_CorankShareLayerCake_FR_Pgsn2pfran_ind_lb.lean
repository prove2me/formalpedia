-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_lb
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_lb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:43.254795+00:00
-- url     : https://prove2.me/theorems/f93d7112-5c39-4ab1-89f7-436d9490c24f
-- title:
--   Pgsn2pfran: ind lb
-- statement:
--   The Pgsn2pfran construction uses the ind lb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L43-L51

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_lb (a xj HH : ℝ) (h : a - HH ≤ xj) (hHH : 0 ≤ HH) :
    a - xj ≤ ∫ τ in (0:ℝ)..HH, (if τ < a - xj then (1:ℝ) else 0) := by sorry
