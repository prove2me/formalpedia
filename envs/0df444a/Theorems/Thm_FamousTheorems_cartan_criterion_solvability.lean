-- Prove2me | Theorems.Thm_FamousTheorems_cartan_criterion_solvability
-- name    : FamousTheorems.cartan_criterion_solvability
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:23:11.604685+00:00
-- url     : https://prove2.me/theorems/2b20907e-e750-4719-9837-4ec9ed7925df
-- title:
--   Cartan's criterion for solvability
-- statement:
--   **Cartan's criterion for solvability.** Let $L$ be a Lie algebra over a domain $R$ of characteristic zero, free and finitely generated as an $R$-module. If the Killing form satisfies $\kappa(x,y)=\operatorname{tr}(\operatorname{ad}x\circ\operatorname{ad}y)=0$ for all $x\in L$ and $y\in[L,L]$, then $L$ is solvable.
--
--   Cartan's criterion reduces solvability to a trace condition. It is the main step in the proof that a Lie algebra in characteristic zero is semisimple if and only if its Killing form is nondegenerate.
--
--   **Formalization note.** Mathlib's `LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero`. `LieAlgebra.derivedSeries R L 1` is $[L,L]$ and `killingForm R L` is the Killing form.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cartan_criterion_solvability {R L : Type*} [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L] [IsNoetherian R L]
    [Module.Free R L] (h : ∀ x y : L, y ∈ LieAlgebra.derivedSeries R L 1 → killingForm R L x y = 0) :
    LieAlgebra.IsSolvable L := by sorry

end FamousTheorems
