-- Prove2me | Theorems.Thm_ChromaticReconstruction_pair_eq_of_second
-- name    : ChromaticReconstruction.pair_eq_of_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T13:53:19.486882+00:00
-- url     : https://prove2.me/theorems/a9475f82-474d-4cc5-98a6-68f61fb19090
-- title:
--   Chromatic Reconstruction: pair eq of second
-- statement:
--   Multiset lemma for the second term of `Θ`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L83-L115
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L83-L115

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.pair_eq_of_second {W : Multiset ℕ} {a b c d r : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hc : 2 ≤ c) (hd : 2 ≤ d)
    (hab : {a, b} ≤ W) (hcd : {c, d} ≤ W) (hrW : r ∈ W - {c, d})
    (h : (c + d) ::ₘ lowerAt (W - {c, d}) r = (a + b - 1) ::ₘ (W - {a, b})) :
    c + d + 1 = a + b ∨ (({c, d} : Multiset ℕ) = {a, b} ∧ r = c + d) := by sorry
