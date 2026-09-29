-- Prove2me | Theorems.Thm_FamousTheorems_abel_ruffini
-- name    : FamousTheorems.abel_ruffini
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:13:52.06359+00:00
-- url     : https://prove2.me/theorems/0cae9fc2-2b46-4f9c-b6b5-37b6c421564e
-- title:
--   The Abel–Ruffini theorem (Galois's criterion: solvable by radicals implies solvable group)
-- statement:
--   **The Abel–Ruffini theorem (Galois's criterion).** Let $E/F$ be a field extension and $x\in E$ solvable by radicals over $F$, i.e. obtainable from $F$ by field operations and extraction of $n$-th roots. If $q\in F[X]$ is irreducible with $q(x)=0$, then the Galois group of $q$ is solvable.
--
--   This is the direction of Galois's criterion that proves Abel–Ruffini: a quintic such as $x^5-4x+2$ over $\mathbb Q$ has Galois group $S_5$, which is not solvable, so its roots cannot be expressed in radicals. It turned the classical question of solving equations into a question about groups and founded Galois theory.
--
--   **Formalization note.** Mathlib's `isSolvable_gal_of_irreducible`. `solvableByRad F E` is the smallest intermediate field closed under taking $n$-th roots, and `q.Gal` is the Galois group of the splitting field of `q`. The non-solvability of $S_5$ is `Equiv.Perm.not_isSolvable_fin_5`, but no specific quintic is treated here.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `isSolvable_gal_of_irreducible`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem abel_ruffini {F E : Type*} [Field F] [Field E] [Algebra F E] {x : E} (hx : x ∈ solvableByRad F E) {q : Polynomial F}
    (hq : Irreducible q) (hqx : Polynomial.aeval x q = 0) : Group.IsSolvable q.Gal := by sorry

end FamousTheorems
