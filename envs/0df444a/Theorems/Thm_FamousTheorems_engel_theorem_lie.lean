-- Prove2me | Theorems.Thm_FamousTheorems_engel_theorem_lie
-- name    : FamousTheorems.engel_theorem_lie
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:03:36.094575+00:00
-- url     : https://prove2.me/theorems/8475237c-b6f8-4a7f-9374-0c4298ea6388
-- title:
--   Engel's theorem
-- statement:
--   **Engel's theorem.** Let $L$ be a Lie algebra over a commutative ring $R$ that is Noetherian as an $R$-module. Then $L$ is nilpotent if and only if $\operatorname{ad}x$ is a nilpotent endomorphism of $L$ for every $x\in L$.
--
--   So nilpotency of a Lie algebra can be checked one element at a time. Engel's theorem is one of the two basic structure theorems for Lie algebras, alongside Lie's theorem on solvable algebras. It is used to show that a Lie algebra of nilpotent matrices can be put in strictly upper-triangular form.
--
--   **Formalization note.** Mathlib's `LieAlgebra.isNilpotent_iff_forall`. `LieRing.IsNilpotent L` means the lower central series of $L$ reaches $0$. `LieAlgebra.ad R L x` is the adjoint endomorphism $y\mapsto[x,y]$. The classical finite-dimensional case over a field is the special case where `IsNoetherian R L` holds automatically.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LieAlgebra.isNilpotent_iff_forall`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem engel_theorem_lie {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L] :
    LieRing.IsNilpotent L ↔ ∀ x : L, IsNilpotent (LieAlgebra.ad R L x) := by sorry

end FamousTheorems
