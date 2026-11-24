-- Prove2me | Theorems.Thm_ChromaticReconstruction_sum_killP1_eq_fP
-- name    : ChromaticReconstruction.sum_killP1_eq_fP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T11:41:09.192804+00:00
-- url     : https://prove2.me/theorems/bdf97b3f-3284-4f76-af52-25872f54c3bd
-- title:
--   Chromatic Reconstruction: sum kill P1 eq f P
-- statement:
--   The identity `∑_{i ∈ s} (w_i - 1) π(p_{w_i - 1} ∏_{j ≠ i} p_{w_j}) = π(Δ P)` for the weights
--   `w_j = m_j + 1` on an index set `s`.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Recovery.lean#L88-L139
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Recovery.lean#L88-L139

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_Theta
import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_Recovery
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
omit [Fintype K]

theorem ChromaticReconstruction.sum_killP1_eq_fP (s : Finset K) (m : K → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) :
    ∑ i ∈ s, (m i : MvPolynomial ℕ ℚ) *
        killP1 (∏ j ∈ s, X ((m j + 1) - if i = j then 1 else 0)) =
      fP (s.val.map fun j => m j + 1) := by sorry
