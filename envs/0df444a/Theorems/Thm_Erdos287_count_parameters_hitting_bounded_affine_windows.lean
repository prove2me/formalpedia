-- Prove2me | Theorems.Thm_Erdos287_count_parameters_hitting_bounded_affine_windows
-- name    : Erdos287.count_parameters_hitting_bounded_affine_windows
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T09:22:03.15172+00:00
-- url     : https://prove2.me/theorems/fe89d903-15bf-53d3-bdd3-869a003ae830
-- title:
--   Counting parameters that hit bounded affine windows
-- statement:
--   Let \(S,G\) be finite sets of natural numbers. For \(j<N\) let \(C_j>0\), and let \(g\) assign an integer position to each index in \(G\). If every \(t\in S\) has \(j<N,i\in G\) with \(C_jt\le g(i)\le C_jt+B\), then \(|S|\le(B+1)N|G|\).
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Affine witness-counting step for the unit-gap argument.

import Mathlib

theorem Erdos287.count_parameters_hitting_bounded_affine_windows (S G : Finset ℕ) (N B : ℕ) (C : Fin N → ℕ) (g : ℕ → ℕ)
    (hC : ∀ j, 0 < C j)
    (hcover : ∀ t ∈ S, ∃ j : Fin N, ∃ i ∈ G, C j * t ≤ g i ∧ g i ≤ C j * t + B) :
    S.card ≤ (B + 1) * N * G.card := by sorry
