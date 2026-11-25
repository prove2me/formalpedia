-- Prove2me | Theorems.Thm_ChromaticReconstruction_coeff_thetaAB_eq_zero
-- name    : ChromaticReconstruction.coeff_thetaAB_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:54:48.576525+00:00
-- url     : https://prove2.me/theorems/8facb88f-e9df-4158-8f10-d2b66d1c0d4d
-- title:
--   Chromatic Reconstruction: coeff theta AB eq zero
-- statement:
--   The Chromatic Reconstruction construction uses the coeff theta AB eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L143-L159
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L143-L159

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.coeff_thetaAB_eq_zero {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a b c d : ℕ}
    (hab : {a, b} ≤ W) (hcd : {c, d} ≤ W) (hne : s(c, d) ≠ s(a, b)) (hle : a + b ≤ c + d) :
    coeff (Multiset.toFinsupp ((a + b - 1) ::ₘ (W - {a, b}))) (thetaAB W c d) = 0 := by sorry
