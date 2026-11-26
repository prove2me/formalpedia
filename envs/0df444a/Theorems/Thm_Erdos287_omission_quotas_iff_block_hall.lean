-- Prove2me | Theorems.Thm_Erdos287_omission_quotas_iff_block_hall
-- name    : Erdos287.omission_quotas_iff_block_hall
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T13:33:18.985679+00:00
-- url     : https://prove2.me/theorems/b95b0a95-e797-4931-b8ce-072bd2857b89
-- title:
--   Hall criterion for nonadjacent omissions with layer quotas
-- statement:
--   Let each available integer carry a layer label, and suppose every run of consecutive available positions has length one or two. Partition the positions into those runs. Given a quota $r_p$ for each label $p$, a set of available positions with no consecutive members meeting the quotas exists exactly when, for every label subset $S$, the blocks containing a label from $S$ number at least $\sum_{p\in S}r_p$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.omission_quotas_iff_block_hall (U P : Finset ℕ) (label block need : ℕ → ℕ)
    (hwithin : ∀ x ∈ U, ∀ y ∈ U, block x = block y →
      x = y ∨ x + 1 = y ∨ y + 1 = x)
    (hbetween : ∀ x ∈ U, x + 1 ∈ U → block x = block (x + 1)) :
    (∃ X ⊆ U, (∀ x ∈ X, x + 1 ∉ X) ∧
      ∀ p ∈ P, need p ≤ (X.filter (fun x => label x = p)).card) ↔
    ∀ S ⊆ P, (∑ p ∈ S, need p) ≤
      ((U.filter (fun x => label x ∈ S)).image block).card := by sorry
