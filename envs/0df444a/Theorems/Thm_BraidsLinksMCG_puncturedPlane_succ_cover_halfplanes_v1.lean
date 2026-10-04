-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlane_succ_cover_halfplanes_v1
-- name    : BraidsLinksMCG.puncturedPlane_succ_cover_halfplanes_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T07:38:27.543991+00:00
-- url     : https://prove2.me/theorems/9979d6ba-89ff-44a8-b998-1ef0a1312830
-- title:
--   A half-plane cover for the punctured-plane induction step
-- statement:
--   Use the two open vertical half-planes at real-coordinate thresholds n+1/2 and n+1 as a cover of the plane with n+1 punctures. Choose a common point in their open overlap, rather than the canonical basepoint, so both cover members and every intersection have the same based point. Both members and every pairwise intersection are path-connected, and the two sets cover the entire punctured plane. This isolates the topology needed by the abstract van Kampen induction step; it does not assert any identification with the named standard loops.
-- source:
--   A. Hatcher, Algebraic Topology, Section 1.2, Theorem 1.20, applied to the two-half-plane cover used in the classical punctured-plane induction. The thresholds are chosen so the overlap is n+1/2 < x < n+1, contains no puncture, and is connected.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem puncturedPlane_succ_cover_halfplanes_v1 (n : ℕ) :
    ∃ (A : Bool → Set (PuncturedPlane (n + 1)))
      (x₀ : PuncturedPlane (n + 1)),
      A Bool.false =
          {z : PuncturedPlane (n + 1) |
            z.1.re < ((n : ℕ) + 1 : ℝ)} ∧
      A Bool.true =
          {z : PuncturedPlane (n + 1) |
            ((n : ℕ) : ℝ) + 1 / 2 < z.1.re} ∧
      (∀ i, x₀ ∈ A i) ∧
      (∀ i, IsOpen (A i)) ∧
      (∀ i, IsPathConnected (A i)) ∧
      (⋃ i, A i) = Set.univ ∧
      (∀ i j, IsPathConnected (A i ∩ A j)) := by sorry

end BraidsLinksMCG
