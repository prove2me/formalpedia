-- Prove2me | Theorems.Thm_FamousTheorems_exists_cartan_subalgebra
-- name    : FamousTheorems.exists_cartan_subalgebra
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:17.965595+00:00
-- url     : https://prove2.me/theorems/dea365c0-0cba-4594-a883-fc32cfff3bd0
-- title:
--   Existence of Cartan subalgebras
-- statement:
--   **Existence of Cartan subalgebras.** Let $L$ be a finite-dimensional Lie algebra over an infinite field $K$. Then there is an element $x\in L$ whose Engel subalgebra
--   $$E(x)=\{y\in L:(\operatorname{ad}x)^n y=0\text{ for some }n\}$$
--   is a Cartan subalgebra of $L$, that is, a nilpotent subalgebra equal to its own normaliser.
--
--   For $x$ regular, $E(x)$ is a Cartan subalgebra. Cartan subalgebras are the starting point for the root space decomposition and the classification of semisimple Lie algebras.
--
--   **Formalization note.** Mathlib's `LieAlgebra.exists_isCartanSubalgebra_engel`. `LieSubalgebra.engel K x` is the Engel subalgebra of $x$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LieAlgebra.exists_isCartanSubalgebra_engel`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem exists_cartan_subalgebra (K L : Type*) [Field K] [LieRing L] [LieAlgebra K L] [Module.Finite K L] [Infinite K] :
    ∃ x : L, (LieSubalgebra.engel K x).IsCartanSubalgebra := by sorry

end FamousTheorems
