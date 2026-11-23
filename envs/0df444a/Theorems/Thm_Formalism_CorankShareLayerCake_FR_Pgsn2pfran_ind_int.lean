-- Prove2me | Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfran_ind_int
-- name    : Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:39.358982+00:00
-- url     : https://prove2.me/theorems/e43eb91f-3017-466d-93a4-09ce1d9f0c9c
-- title:
--   Pgsn2pfran: ind int
-- statement:
--   The Pgsn2pfran construction uses the ind int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CorankShare/CorankShareProofs/LayerCakeFormula.lean#L20-L41

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

theorem Formalism.CorankShareLayerCake.FR.Pgsn2pfran.ind_int (c HH : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ HH) :
    ∫ τ in (0:ℝ)..HH, (if τ < c then (1:ℝ) else 0) = c := by sorry
