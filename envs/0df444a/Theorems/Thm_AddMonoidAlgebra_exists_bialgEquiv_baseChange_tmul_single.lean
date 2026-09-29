-- Prove2me | Theorems.Thm_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single
-- name    : AddMonoidAlgebra.exists_bialgEquiv_baseChange_tmul_single
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/6bf57aa6-6d41-515e-bf48-d908c4ac2fd1
-- title:
--   Base change of a monoid algebra is a bialgebra isomorphism
-- statement:
--   Let $R$ and $S$ be commutative rings with $S$ an $R$-algebra, and let $G$ be an additive commutative monoid. The theorem asserts the existence of an isomorphism of $S$-bialgebras $e : S \otimes_R R[G] \xrightarrow{\sim} S[G]$, where $R[G]$ and $S[G]$ are the additive monoid algebras `AddMonoidAlgebra R G` and `AddMonoidAlgebra S G` with their Mathlib bialgebra structures (group-like on the basis elements: $\varepsilon(\mathrm{single}\,g\,1)=1$ and $\Delta(\mathrm{single}\,g\,1)=\mathrm{single}\,g\,1\otimes \mathrm{single}\,g\,1$), the source carrying the $S$-bialgebra structure obtained by base change along $R \to S$, such that on pure tensors of basis elements $e$ is given by $e(s \otimes \mathrm{single}\,g\,r) = \mathrm{single}\,g\,(r \cdot s)$ for all $s \in S$, $g \in G$ and $r \in R$. The statement is an existence assertion pinned down by this formula rather than the construction of a named isomorphism; the isomorphism is in particular $S$-algebra linear and compatible with counit and comultiplication.
--
--   This is the standard compatibility of the canonical base-change isomorphism $S \otimes_R R[G] \cong S[G]$ of monoid algebras with the bialgebra structures, i.e. the statement that base change of the coordinate ring of a constant (diagonalisable) group scheme is a bialgebra isomorphism. It is used in [`ModularCurve.nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness`](thm.html#ModularCurve.nonempty_bialgEquiv_baseChange_residueField_torusQuotient_one_addMonoidAlgebra_of_finPtsWitness) to identify the base change to a residue field of a group algebra over the base with the corresponding group algebra over that residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddMonoidAlgebra_exists_bialgEquiv_baseChange_tmul_single.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem AddMonoidAlgebra.exists_bialgEquiv_baseChange_tmul_single
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [AddCommMonoid G] :
    ∃ e : S ⊗[R] AddMonoidAlgebra R G ≃ₐc[S] AddMonoidAlgebra S G,
      ∀ (s : S) (g : G) (r : R), e (s ⊗ₜ AddMonoidAlgebra.single g r) = AddMonoidAlgebra.single g (r • s) := by sorry
