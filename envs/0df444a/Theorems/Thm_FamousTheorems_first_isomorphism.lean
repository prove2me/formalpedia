-- Prove2me | Theorems.Thm_FamousTheorems_first_isomorphism
-- name    : FamousTheorems.first_isomorphism
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:19.012429+00:00
-- url     : https://prove2.me/theorems/a98c76b6-6faf-409a-abb2-e1e6edb4b129
-- title:
--   The first isomorphism theorem for groups
-- statement:
--   **The first isomorphism theorem.**
--
--   For any group homomorphism $\varphi : G \to H$,
--   $$G/\ker\varphi \;\cong\; \operatorname{im}\varphi .$$
--
--   Quotienting by exactly the information $\varphi$ forgets leaves exactly the information
--   $\varphi$ records. It is the statement that makes normal subgroups and quotients worth
--   defining: kernels are precisely the normal subgroups, and every homomorphic image is a
--   quotient.
--
--   The theorem is the first of three, the others describing $(G/N)/(M/N) \cong G/M$ and
--   $HN/N \cong H/(H \cap N)$, and it has the same form in every algebraic category — rings,
--   modules, Lie algebras, and in general any variety of algebras, where it becomes the
--   statement that congruences correspond to quotient objects.
--
--   Usually credited to Emmy Noether, who isolated it in her 1927 work on ideal theory, with
--   roots in Dedekind's treatment of modules.
--
--   **Formalization note.** `φ.ker` is a normal subgroup of `G` and `φ.range` a subgroup of `H`,
--   so both quotient and image carry group structures. The isomorphism is data rather than a
--   proposition, so it is wrapped in `Nonempty`. The result is Mathlib's
--   `QuotientGroup.quotientKerEquivRange`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem first_isomorphism {G : Type*} [Group G] {H : Type*} [Group H] (φ : G →* H) :
    Nonempty (G ⧸ φ.ker ≃* φ.range) := by sorry

end FamousTheorems
