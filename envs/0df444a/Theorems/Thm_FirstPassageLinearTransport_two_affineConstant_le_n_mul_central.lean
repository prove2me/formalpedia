-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_affineConstant_le_n_mul_central
-- name    : FirstPassageLinearTransport.two_affineConstant_le_n_mul_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:06:39.953587+00:00
-- url     : https://prove2.me/theorems/a76bf8cb-3b87-43cd-8d47-e4dbd4f102a8
-- title:
--   First Passage Linear Transport: two affine Constant le n mul central
-- statement:
--   The First Passage Linear Transport construction uses the two affine Constant le n mul central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L407-L450
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Envelope.lean#L407-L450

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section

theorem FirstPassageLinearTransport.two_affineConstant_le_n_mul_central
    {n k M : ℕ} (hM : 4 ≤ M) (hkM : k ≤ M)
    (hnShell : n ∈ dyadicShell M) :
    2 * (2 + Real.sqrt 3) ≤ (n : ℝ) * centralOrbitScale k := by sorry
