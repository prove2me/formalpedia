-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit
-- name    : FirstPassageLinearTransport.exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:57.816842+00:00
-- url     : https://prove2.me/theorems/df86dc32-1d16-51a3-8b5e-3d80fd7dcc88
-- title:
--   First Passage Linear Transport: exists orbit gt mul of mem shell Prefix Multiplicative Hit
-- statement:
--   The First Passage Linear Transport construction uses the exists orbit gt mul of mem shell Prefix Multiplicative Hit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L157-L173
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ReciprocalHeightObstruction.lean#L157-L173

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ}
    {n : {n : ℕ // n ∈ dyadicShell M}}
    (hn : n ∈ shellPrefixMultiplicativeHit M h hhM u) :
    ∃ j : ℕ, j ≤ h ∧ u * (n.1 : ℝ) < (orbit j n.1 : ℝ) := by sorry
