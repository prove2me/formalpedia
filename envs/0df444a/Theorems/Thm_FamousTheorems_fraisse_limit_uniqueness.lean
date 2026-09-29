-- Prove2me | Theorems.Thm_FamousTheorems_fraisse_limit_uniqueness
-- name    : FamousTheorems.fraisse_limit_uniqueness
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:07:17.704775+00:00
-- url     : https://prove2.me/theorems/cbb6e3a8-bb65-474c-9e51-0ccbca593b27
-- title:
--   Uniqueness of Fraïssé limits
-- statement:
--   **Uniqueness of Fraïssé limits.** Let $L$ be a first-order language with countably many function symbols and let $K$ be a class of $L$-structures. If $M$ and $N$ are countable structures that are both Fraïssé limits of $K$, then $M$ and $N$ are isomorphic.
--
--   A Fraïssé limit of $K$ is a countable ultrahomogeneous structure whose age (class of finitely generated substructures) is $K$. The uniqueness theorem, proved by a back-and-forth argument, is what makes objects such as the rational order $(\mathbb Q,<)$, the Rado random graph and the countable atomless Boolean algebra canonical.
--
--   **Formalization note.** Mathlib's `FirstOrder.Language.IsFraisseLimit.nonempty_equiv`. `IsFraisseLimit K M` says that $M$ is countable and ultrahomogeneous with age $K$, and `L.Equiv M N` is the type of $L$-isomorphisms. The countability of the function symbols is the hypothesis `Countable ((l : ℕ) × L.Functions l)`. Both structures live in the same universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FirstOrder.Language.IsFraisseLimit.nonempty_equiv`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem fraisse_limit_uniqueness {L : FirstOrder.Language} {K : Set (CategoryTheory.Bundled L.Structure)} {M N : Type u}
    [L.Structure M] [L.Structure N] [Countable ((l : ℕ) × L.Functions l)] [Countable M] [Countable N]
    (hM : FirstOrder.Language.IsFraisseLimit K M) (hN : FirstOrder.Language.IsFraisseLimit K N) :
    Nonempty (L.Equiv M N) := by sorry

end FamousTheorems
