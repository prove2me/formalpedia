-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_subsets_liminf_encard
-- name    : AvramDividend.Classical.avram_p2_34dbea70_finite_subsets_liminf_encard
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:56:54.479675+00:00
-- url     : https://prove2.me/theorems/138eb8ef-d854-425f-b0c8-1cfb7acc8e43
-- title:
--   Eventual counting of every finite subset bounds the full extended cardinality
-- statement:
--   If S is an arbitrary set and every finite subset of S has cardinality bounded by a varying natural number sequence for all sufficiently large indices, then the extended cardinality of S is bounded by the limit inferior of those counts in the extended natural numbers. The result handles infinite S without assuming any finite activity. It is a generic deterministic combinatorial bridge from finite jump-time selections to full marked-jump counts.

import Mathlib

open Filter

theorem AvramDividend.Classical.avram_p2_34dbea70_finite_subsets_liminf_encard {α : Type*}
    (S : Set α) (g : ℕ → ℕ)
    (h : ∀ F : Finset α, (F : Set α) ⊆ S →
      ∀ᶠ n : ℕ in atTop, F.card ≤ g n) :
    S.encard ≤ Filter.liminf (fun n : ℕ => (g n : ℕ∞)) atTop := by sorry
