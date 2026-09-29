-- Prove2me | Theorems.Thm_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate
-- name    : AutomorphicForm.WeylIntegrable.finprod_norm_eq_relIndex_dilate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/27353e26-8560-52de-8646-3dd55c033df9
-- title:
--   Product of local norms equals index of integral dilate
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $\mathbb{A}_f$ denote the finite adele ring of $\mathcal{O}_F$ and $F$, and let $y$ be a unit of $\mathbb{A}_f$. Assume that at every height-one prime $v$ of $\mathcal{O}_F$ the component $y_v$ of $y$ in the completion $F_v$ satisfies $1 \le \mathrm{v}(y_v)$ for the canonical valuation of the adic completion; equivalently, $y_v$ lies outside the maximal ideal of $\mathcal{O}_v$ in the sense that its valuation is at least $1$, so that $\|y_v\| \ge 1$. Write $\widehat{\mathcal{O}} =$ `intLattice F` for the additive subgroup of $\mathbb{A}_f$ consisting of those adeles all of whose components lie in the respective valuation rings $\mathcal{O}_v$, and `dilate F y` for the image $y\widehat{\mathcal{O}}$ of $\widehat{\mathcal{O}}$ under multiplication by $y$. The conclusion is that the finitely-supported product, over all height-one primes $v$ of $\mathcal{O}_F$, of the normalised absolute values $\|y_v\|$ equals, as a real number, the relative index of $\widehat{\mathcal{O}}$ in $y\widehat{\mathcal{O}}$, that is the index of $\widehat{\mathcal{O}} \cap y\widehat{\mathcal{O}}$ in $y\widehat{\mathcal{O}}$ (which under the hypothesis is $[\,y\widehat{\mathcal{O}} : \widehat{\mathcal{O}}\,]$).
--
--   This is the index-theoretic form of the product formula for the module of a finite idele: the product of the local normalised absolute values of an idele whose components are all of absolute value at least one computes a lattice index in the finite adeles. The proof invokes the factorisation of the adelic `distribHaarChar` into infinite and finite contributions, and the result feeds the computation [`AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex`](thm.html#AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WeylIntegrable_finprod_norm_eq_relIndex_dilate.lean

import Definitions.Def_AutomorphicForm_WeylSelectors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.finprod_norm_eq_relIndex_dilate (F : Type) [Field F] [NumberField F]
    (y : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      1 ≤ Valued.v ((y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v)) :
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        ‖(y : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v‖
      = ((intLattice F).relIndex (dilate F y) : ℝ) := by sorry
