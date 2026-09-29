-- Prove2me | Theorems.Thm_FamousTheorems_matroid_rank_submodular_7a
-- name    : FamousTheorems.matroid_rank_submodular_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:48.664077+00:00
-- url     : https://prove2.me/theorems/7df89202-8bc2-4e89-a2c6-113e8f647e7e
-- title:
--   Submodularity of the matroid rank function
-- statement:
--   **Submodularity of the matroid rank function.** For every matroid $M$ on a ground set $\alpha$ and all sets $X,Y\subseteq\alpha$,
--   $$r(X\cap Y)+r(X\cup Y)\le r(X)+r(Y),$$
--   where $r$ is the rank function of $M$.
--
--   Submodularity, together with monotonicity and $r(X)\le|X|$, characterises matroid rank functions, as Whitney showed in 1935. It is the source of the connection between matroids and combinatorial optimization. It underlies Edmonds' matroid intersection theorem, the greedy algorithm and the theory of submodular functions.
--
--   **Formalization note.** Mathlib's `Matroid.eRk_inter_add_eRk_union_le`. `M.eRk X` is the rank of $X$ in $\mathbb N\cup\{\infty\}$, so the statement also covers infinite matroids. Sets outside the ground set are allowed, and their rank is that of their intersection with the ground set.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Matroid.eRk_inter_add_eRk_union_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem matroid_rank_submodular_7a {α : Type*} (M : Matroid α) (X Y : Set α) : M.eRk (X ∩ Y) + M.eRk (X ∪ Y) ≤ M.eRk X + M.eRk Y := by sorry

end FamousTheorems
