-- Prove2me | Theorems.Thm_FamousTheorems_nobeling_theorem
-- name    : FamousTheorems.nobeling_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:23.056875+00:00
-- url     : https://prove2.me/theorems/c1a70826-3792-4018-9ae8-4ca0947479dc
-- title:
--   Nöbeling's theorem
-- statement:
--   **Nöbeling's theorem.** For every compact, Hausdorff, totally disconnected space $X$, the group $C(X,\mathbb Z)$ of locally constant integer-valued functions on $X$ is a free abelian group.
--
--   Nöbeling proved this in 1968, answering a question of Specker. In particular, the group of bounded functions $\mathbb N\to\mathbb Z$ is free abelian, although the group $\mathbb Z^{\mathbb N}$ of all such functions is not. The theorem is also used in condensed mathematics (Clausen–Scholze).
--
--   **Formalization note.** Mathlib's `LocallyConstant.freeOfProfinite`, stated for objects of the category `Profinite` and applied here to `Profinite.of X`. Compact Hausdorff totally disconnected spaces are exactly the profinite spaces. `LocallyConstant X ℤ` is the group of locally constant functions, and `Module.Free ℤ` says that it has a basis as a $\mathbb Z$-module.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LocallyConstant.freeOfProfinite`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nobeling_theorem {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    Module.Free ℤ (LocallyConstant X ℤ) := by sorry

end FamousTheorems
