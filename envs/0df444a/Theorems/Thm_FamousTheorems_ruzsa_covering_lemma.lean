-- Prove2me | Theorems.Thm_FamousTheorems_ruzsa_covering_lemma
-- name    : FamousTheorems.ruzsa_covering_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:57.030984+00:00
-- url     : https://prove2.me/theorems/ffb963a6-7641-4910-8207-32f6e6b0aa2e
-- title:
--   The Ruzsa covering lemma
-- statement:
--   **The Ruzsa covering lemma.** Let $A,B$ be finite subsets of a group, not necessarily abelian but written additively, $B\neq\emptyset$, with $|A+B|\le K|B|$. Then there is $F\subseteq A$ with $|F|\le K$ and
--   $$A\subseteq F+(B-B).$$
--
--   So a set with small sumset relative to $B$ is covered by few translates of $B-B$. It is one of the basic tools of additive combinatorics, used in Freiman's theorem and in the passage between approximate groups and sets of small doubling.
--
--   **Formalization note.** Mathlib's `Finset.ruzsa_covering_add` (the additive form of `Finset.ruzsa_covering_mul`). The group is an arbitrary additive group, sumsets and difference sets are pointwise, and $K$ is real.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.ruzsa_covering_add`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped Pointwise

theorem ruzsa_covering_lemma {G : Type*} [AddGroup G] [DecidableEq G] {A B : Finset G} {K : ℝ} (hB : B.Nonempty)
    (hK : ((A + B).card : ℝ) ≤ K * B.card) : ∃ F ⊆ A, (F.card : ℝ) ≤ K ∧ A ⊆ F + (B - B) := by sorry

end FamousTheorems
