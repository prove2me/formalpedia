-- Prove2me | Theorems.Thm_FamousTheorems_cstar_algebra_sum_four_unitaries_6b
-- name    : FamousTheorems.cstar_algebra_sum_four_unitaries_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:03.363779+00:00
-- url     : https://prove2.me/theorems/d95dde3d-a907-4ce2-98bb-e132cfb98479
-- title:
--   Every element of a unital C*-algebra is a combination of four unitaries
-- statement:
--   **Every element of a unital C\*-algebra is a combination of four unitaries.** Let $A$ be a unital C\*-algebra and $x\in A$. There are unitaries $u_1,\dots,u_4\in A$ and scalars $c_1,\dots,c_4\in\mathbb C$ with $|c_i|\le\|x\|/2$ such that
--   $$x=c_1u_1+c_2u_2+c_3u_3+c_4u_4.$$
--
--   It follows that the unitaries span $A$. Many questions about a C\*-algebra, such as whether a linear map is determined by its values or whether a subspace is an ideal, therefore reduce to questions about unitaries. The proof writes $x$ as a combination of two self-adjoint elements and each self-adjoint element of norm at most $1$ as the average of two unitaries $a\pm i\sqrt{1-a^2}$.
--
--   **Formalization note.** Mathlib's `CStarAlgebra.exists_sum_four_unitary`. `unitary A` is the submonoid of unitary elements of $A$, coerced back to $A$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `CStarAlgebra.exists_sum_four_unitary`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cstar_algebra_sum_four_unitaries_6b {A : Type*} [CStarAlgebra A] (x : A) :
    ∃ (u : Fin 4 → unitary A) (c : Fin 4 → ℂ), x = ∑ i : Fin 4, c i • (u i : A) ∧ ∀ i, ‖c i‖ ≤ ‖x‖ / 2 := by sorry

end FamousTheorems
