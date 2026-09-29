-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
-- name    : AlgebraicGeometry.Scheme.nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/b480c6a0-a3eb-5d4a-8525-2b2ddf8fe9da
-- title:
--   An integer killing all sections kills fppf cohomology
-- statement:
--   Let $S$ be a scheme (with underlying data in universe $u$) and let $F$ be a sheaf of abelian groups, valued in $\mathrm{Ab}$ at level $u+1$, on the small fppf site of $S$: its underlying category $S.Fppf$ is the category of objects $U \to S$ over $S$ whose structure morphism is flat and locally of finite presentation (no condition on the other leg), equipped with the Grothendieck topology `smallFppfTopology S` attached to this morphism property. Let $k$ be a natural number, and assume that for every object $U$ of $S.Fppf$ and every section $s \in F(U)$ one has $k \cdot s = 0$, i.e. $k$ annihilates all sections of $F$ over all objects of the site. Then for every $n : \mathbb{N}$ and every class $x$ in `fppfCohomology S F n`, which is by definition the sheaf cohomology group $F.H\,n$, the $\mathrm{Ext}^n$-group from the constant sheaf $\underline{\mathbb{Z}}$ to $F$ in the category of abelian sheaves on this site, one has $k \cdot x = 0$.
--
--   This is the elementary additivity statement that multiplication by $k$ on an abelian fppf sheaf induces multiplication by $k$ on its fppf cohomology, so that an exponent for the sections is an exponent for all cohomology groups. It is used in the torsion estimates for $J_0$, notably by [`ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow`](thm.html#ModularCurve.JZeroNeronPrimaryTorsionCore.exists_natCard_fppfCohomology_one_eq_pow), to bound exponents of fppf cohomology of finite flat group schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero.lean

import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.nsmul_fppfCohomology_eq_zero_of_nsmul_sections_eq_zero
    (S : Scheme.{u}) (F : Sheaf (smallFppfTopology S) Ab.{u + 1}) (k : ℕ)
    (hF : ∀ (U : S.Fppf) (s : F.1.obj (Opposite.op U)), k • s = 0)
    (n : ℕ) (x : fppfCohomology S F n) :
    k • x = 0 := by sorry
