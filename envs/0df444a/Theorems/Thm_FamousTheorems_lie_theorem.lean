-- Prove2me | Theorems.Thm_FamousTheorems_lie_theorem
-- name    : FamousTheorems.lie_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T09:15:07.230238+00:00
-- url     : https://prove2.me/theorems/665bf35b-98cf-4d2a-9798-4ab3e6184b60
-- title:
--   Lie's theorem on solvable Lie algebras
-- statement:
--   **Lie's theorem.** Let $L$ be a solvable Lie algebra over a field $k$ of characteristic $0$ and $V$ a nonzero finite-dimensional $L$-module on which $L$ is triangularizable (e.g. $k$ algebraically closed). Then $L$ has a common eigenvector in $V$: there is a linear functional $\chi$ on $L$ whose weight space $\{v : x\cdot v=\chi(x)v\ \forall x\}$ is nonzero.
--
--   By induction this puts every such representation in upper-triangular form. It is the solvable counterpart of Engel's theorem and a basic structural tool (Borel subalgebras, Cartan's criterion, the Levi decomposition).
--
--   **Formalization note.** Mathlib's `LieModule.exists_nontrivial_weightSpace_of_isSolvable`; `LieModule.IsTriangularizable` asks that each $x\in L$ act with all eigenvalues in $k$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LieModule.exists_nontrivial_weightSpace_of_isSolvable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem lie_theorem (k : Type*) [Field k] (L : Type*) [LieRing L] [LieAlgebra k L] (V : Type*) [AddCommGroup V]
    [Module k V] [LieRingModule L V] [LieModule k L V] [CharZero k] [Module.Finite k V] [Nontrivial V]
    [LieAlgebra.IsSolvable L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, Nontrivial (LieModule.weightSpace V ⇑χ) := by sorry

end FamousTheorems
