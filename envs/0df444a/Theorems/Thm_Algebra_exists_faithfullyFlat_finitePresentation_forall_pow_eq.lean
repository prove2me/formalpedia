-- Prove2me | Theorems.Thm_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq
-- name    : Algebra.exists_faithfullyFlat_finitePresentation_forall_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/507ff26d-2a70-5f64-874e-a8fb6fe9c87f
-- title:
--   Extracting m-th roots of finitely many units fppf-locally
-- statement:
--   Let $R$ be a commutative ring, let $m$ be a natural number with $0 < m$, let $\iota$ be a finite type and let $u : \iota \to R^{\times}$ be a family of units of $R$. The theorem asserts the existence of a type $R'$ in the same universe as $R$, together with a commutative ring structure on $R'$ and an $R$-algebra structure, such that $R'$ is faithfully flat as an $R$-module and finitely presented as an $R$-algebra, and such that there is a family $v : \iota \to R'^{\times}$ of units of $R'$ with $(v\,i)^{m} = \mathrm{algebraMap}\,R\,R'\,(u\,i)$ in $R'$ for every $i \in \iota$, the equation being between elements of $R'$, the left-hand side being the $m$-th power of the underlying element of the unit $v\,i$ and the right-hand side the image of the underlying element of $u\,i$ under the structure map. No assumption is made on $m$ beyond positivity; in particular $m$ need not be invertible in $R$, so the extension produced is flat and finitely presented but not in general étale.
--
--   This is the fppf Kummer covering used to extract $m$-th roots of a finite family of units: the standard fact that $R[x_i]/(x_i^m - u_i)$ is a finite free, hence faithfully flat, finitely presented $R$-algebra over which each $u_i$ becomes an $m$-th power. It is invoked in [`AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp`](thm.html#AlgebraicGeometry.SplitTorus.exists_flat_surjective_pow_eq_comp), where multiplication by $m$ on a split torus is shown to be covered flatly and surjectively.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_exists_faithfullyFlat_finitePresentation_forall_pow_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem Algebra.exists_faithfullyFlat_finitePresentation_forall_pow_eq
    {R : Type u} [CommRing R] (m : ℕ) (hm : 0 < m) {ι : Type} [Finite ι] (u : ι → Rˣ) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Module.FaithfullyFlat R R' ∧ Algebra.FinitePresentation R R' ∧
      ∃ v : ι → R'ˣ, ∀ i, (v i : R') ^ m = algebraMap R R' (u i) := by sorry
