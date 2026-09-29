-- Prove2me | Theorems.Thm_FamousTheorems_marica_schonheim_inequality
-- name    : FamousTheorems.marica_schonheim_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:35.627464+00:00
-- url     : https://prove2.me/theorems/6f30f3a4-bab7-49f8-a827-da54429c47dc
-- title:
--   The Marica–Schönheim inequality
-- statement:
--   **The Marica–Schönheim inequality.** Let $\mathcal F$ be a finite family of elements of a generalised Boolean algebra, for example a finite family of sets. Then the family of differences $\{A\setminus B: A,B\in\mathcal F\}$ has at least as many elements as $\mathcal F$:
--   $$|\mathcal F|\le|\mathcal F\setminus\mathcal F|.$$
--
--   Marica and Schönheim proved it in 1969 and used it to settle the squarefree case of Graham's conjecture on greatest common divisors: for squarefree positive integers $a_1<\dots<a_n$, some quotient $a_i/\gcd(a_i,a_j)$ is at least $n$.
--
--   **Formalization note.** Mathlib's `Finset.card_le_card_diffs`. `s.diffs s` is the finset $\{a\setminus b: a,b\in s\}$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.card_le_card_diffs`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem marica_schonheim_inequality {α : Type*} [DecidableEq α] [GeneralizedBooleanAlgebra α] (s : Finset α) : s.card ≤ (s.diffs s).card := by sorry

end FamousTheorems
