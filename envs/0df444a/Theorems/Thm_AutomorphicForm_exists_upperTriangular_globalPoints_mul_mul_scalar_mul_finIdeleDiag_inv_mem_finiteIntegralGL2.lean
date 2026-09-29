-- Prove2me | Theorems.Thm_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
-- name    : AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/bf6a6016-5387-53b5-bd59-7b02dffd854f
-- title:
--   Class criterion for an upper-triangular adelic decomposition
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $g$ be an element of $\mathrm{GL}_2$ over the finite adele ring $\mathbb{A}_F^{f}$ of $\mathcal{O}_F$ in $F$, and let $a,d$ be units of $\mathbb{A}_F^{f}$. Assume, first, that for every height one prime $v$ of $\mathcal{O}_F$ the valuation at $v$ of the $v$-component of $d$ equals the maximum of the valuations of the $v$-components of $g_{10}a^{-1}$ and of $g_{11}$, the entries of the bottom row of $g\cdot\mathrm{diag}(a,1)^{-1}$; and, second, that $c(a)\cdot c(d)^2 = c(\det g)$ in the ideal class group of $\mathcal{O}_F$, where $c =$ [`AutomorphicForm.contentHomFin`](def/AutomorphicForm_ProductionPinsGeneral.html#L119) is the homomorphism sending a finite idele $\delta$ to the class of the fractional ideal $\prod_v v^{\,\mathrm{ord}_v(\delta)}$ (the finite product over height one primes of $v$ raised to the exponent `finIdeleExponentAt` of $\delta$ at $v$). Then there exist $b\in\mathrm{GL}_2(F)$ with $b_{10}=0$ and a unit $s$ of $\mathbb{A}_F^{f}$ such that the product of the entrywise image of $b$ in $\mathrm{GL}_2(\mathbb{A}_F^{f})$, of $g$, of the scalar matrix $s\cdot\mathrm{Id}$ and of the inverse of $\mathrm{diag}(a,1)$ lies in the subgroup [`NumberField.AdelicLevel.finiteIntegralGL2`](def/NumberField_AdelicLevel.html#L443), that is, `finiteLevelZero` for the ideal $\top$: both that product and its inverse satisfy the predicate `IsLevelZeroMatrix` at level $\top$.
--
--   This is the reduction step underlying the decomposition of $\mathrm{GL}_2(\mathbb{A}_F^{f})$ into classes indexed by the ideal class group: a congruence of ideal classes involving $\det g$, the idele $a$ and the content $d$ of the bottom row of $g\cdot\mathrm{diag}(a,1)^{-1}$ forces $g$ to lie in $B(F)\cdot\mathrm{GL}_2$-integral $\cdot\,\mathrm{diag}(a,1)$ up to the centre, with $B(F)$ the global upper triangular matrices. Only this implication is asserted, and the content is carried by the idele $d$ together with the valuation hypothesis rather than by a fractional ideal; it is used in [`AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet`](thm.html#AutomorphicForm.SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet), the statement that finitely many translates of a Siegel set cover $\mathrm{GL}_2$ of the adeles modulo the global points and the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
    (F : Type) [Field F] [NumberField F]
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
    (a d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
              ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v)))
    (hcls : AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
      AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
              (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F b) * g *
            Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
            (AutomorphicForm.finIdeleDiag F a))⁻¹
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers F) F := by sorry
