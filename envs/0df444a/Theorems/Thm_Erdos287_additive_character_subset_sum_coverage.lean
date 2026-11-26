-- Prove2me | Theorems.Thm_Erdos287_additive_character_subset_sum_coverage
-- name    : Erdos287.additive_character_subset_sum_coverage
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:04:45.811794+00:00
-- url     : https://prove2.me/theorems/c0897e7b-fb5d-4ac1-bd47-de516fd87fc1
-- title:
--   Additive character criterion for covering all residues with subset sums
-- statement:
--   Let $D$ be a finite set with weights $w_n$ in $\mathbb Z/q\mathbb Z$ for $q>0$, and let $\chi$ be the standard additive character. If $\sum_{a\ne0}|\prod_{n\in D}(1+\chi(aw_n))|<2^{|D|}$, then each residue $t$ is a sum $\sum_{n\in T}w_n$ for some $T\subseteq D$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.additive_character_subset_sum_coverage (q : ℕ) [NeZero q] (D : Finset ℕ) (w : ℕ → ZMod q)
    (t : ZMod q)
    (hsmall : (∑ a ∈ (Finset.univ.erase (0 : ZMod q)),
      ‖∏ n ∈ D, (1 + ZMod.stdAddChar (a * w n))‖) < (2 : ℝ) ^ D.card) :
    ∃ T ⊆ D, (∑ n ∈ T, w n) = t := by sorry
