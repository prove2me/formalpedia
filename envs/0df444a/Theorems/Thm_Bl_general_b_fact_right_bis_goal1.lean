-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_bis_goal1
-- name    : Bl.general_b_fact_right_bis.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:31.877982+00:00
-- url     : https://prove2.me/theorems/656dbd08-d3ea-4d8a-a39e-04a66ea24244
-- title:
--   general b fact right bis: goal1
-- statement:
--   The general b fact right bis construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBis/Imports.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightBis/Imports.lean#L7-L16

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightBis_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial ComplexOrder
open Bl Bl.general_b_fact_right_bis

theorem Bl.general_b_fact_right_bis.goal1 {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (μ : ℂ) (hμ : G.charpoly.IsRoot μ) :
    ∃ v : Fin k → ℂ, v ≠ 0 ∧ G *ᵥ v = μ • v := by sorry
