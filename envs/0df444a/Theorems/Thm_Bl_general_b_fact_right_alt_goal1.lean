-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_alt_goal1
-- name    : Bl.general_b_fact_right_alt.goal1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:13.65179+00:00
-- url     : https://prove2.me/theorems/7c0156a9-8786-40b8-9028-9e4f1afc8e1d
-- title:
--   general b fact right alt: goal1
-- statement:
--   The general b fact right alt construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightAlt/Imports.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightAlt/Imports.lean#L7-L18

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open Bl Bl.general_b_fact_right_alt

theorem Bl.general_b_fact_right_alt.goal1 {K S : Type*} [CommRing K] [CommRing S] [Algebra K S] {ι : Type*} [Fintype ι]
    {G : MvPolynomial ι K} {d : ℕ} (hG : IsHomogeneous G d) (c : S) (f : ι → S) :
    aeval (fun v => c * f v) G = c ^ d * aeval f G := by sorry
