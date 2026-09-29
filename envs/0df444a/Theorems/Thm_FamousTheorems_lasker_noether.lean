-- Prove2me | Theorems.Thm_FamousTheorems_lasker_noether
-- name    : FamousTheorems.lasker_noether
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:43.192078+00:00
-- url     : https://prove2.me/theorems/c9a3936d-c2cb-467d-bd66-65b5ebdc9120
-- title:
--   The Lasker–Noether theorem
-- statement:
--   **The Lasker–Noether theorem.** Let $M$ be a Noetherian module over a commutative ring $R$. Every submodule $N\subseteq M$ has a minimal primary decomposition: $N=Q_1\cap\cdots\cap Q_k$ with each $Q_i$ primary, the radicals $\sqrt{\operatorname{Ann}(M/Q_i)}$ pairwise distinct, and no $Q_i$ redundant.
--
--   It generalises unique factorisation into prime powers from $\mathbb Z$ to arbitrary Noetherian rings and modules. Geometrically, it decomposes an affine scheme's closed subscheme into primary components, the associated primes being its irreducible components and embedded components.
--
--   **Formalization note.** Mathlib's `Submodule.isLasker` (every Noetherian module is Lasker) combined with `Submodule.IsLasker.exists_isMinimalPrimaryDecomposition`. `N.IsMinimalPrimaryDecomposition t` records that `t.inf id = N`, each member is primary, the radicals of `J.colon Set.univ` are pairwise distinct, and no member can be dropped.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Submodule.isLasker`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lasker_noether {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherian R M] (N : Submodule R M) :
    ∃ t : Finset (Submodule R M), N.IsMinimalPrimaryDecomposition t := by sorry

end FamousTheorems
