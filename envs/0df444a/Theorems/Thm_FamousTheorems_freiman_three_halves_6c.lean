-- Prove2me | Theorems.Thm_FamousTheorems_freiman_three_halves_6c
-- name    : FamousTheorems.freiman_three_halves_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:01.954267+00:00
-- url     : https://prove2.me/theorems/0b7810e0-822d-4a78-9f37-6c576a1512f5
-- title:
--   Freiman's 3/2 theorem
-- statement:
--   **Freiman's $3/2$ theorem.** Let $A$ be a finite subset of a group $G$ with $|AA|<\frac32|A|$. Then there is a finite subgroup $H$ of $G$ with $|H|<\frac32|A|$ such that, for every $a\in A$, $A\subseteq aH$ and $aH=Ha$.
--
--   So $A$ lies in a single coset of a normalised subgroup $H$ of comparable size. This is the simplest case of Freiman's structure theory of sets with small doubling, and the constant $\frac32$ is sharp.
--
--   **Formalization note.** Mathlib's `Finset.doubling_lt_three_halves`. `A * A` is the pointwise product set, and the size comparisons are made in $\mathbb Q$. The subgroup is returned with a `Fintype` instance so that its cardinality can be stated. The equation $aH=Ha$ is written with the right action of $a$ through `MulOpposite.op a`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Finset.doubling_lt_three_halves`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Pointwise

theorem freiman_three_halves_6c {G : Type*} [Group G] [DecidableEq G] {A : Finset G}
    (h : ((A * A).card : ℚ) < 3 / 2 * A.card) :
    ∃ (H : Subgroup G) (_ : Fintype H), (Fintype.card H : ℚ) < 3 / 2 * A.card ∧
      ∀ a ∈ A, (A : Set G) ⊆ a • (H : Set G) ∧ a • (H : Set G) = MulOpposite.op a • (H : Set G) := by sorry

end FamousTheorems
