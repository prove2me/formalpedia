-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_fppfCohomology_kernel_zsmul_eq_zero
-- name    : AlgebraicGeometry.Scheme.fppfCohomology_kernel_zsmul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/4f0abb44-69c2-565f-a240-128e1740a254
-- title:
--   fppf cohomology of G[n] is killed by n
-- statement:
--   Let $S=\operatorname{Spec}\mathbf Z$, presented as the scheme `specInt`, and let its small fppf site be the category `S.Fppf` of $S$-schemes whose structure morphism is flat and locally of finite presentation, equipped with the Grothendieck topology `smallFppfTopology`. Let $G$ be a sheaf of abelian groups on this site, let $n$ be an integer — no positivity, invertibility or other condition is imposed — and let $k$ be a natural number. Inside the abelian category of such sheaves form the endomorphism $n \cdot \mathrm{id}_G$ and its kernel $\ker(n \cdot \mathrm{id}_G)$, that is the $n$-torsion subsheaf $G[n]$. The group `fppfCohomology specInt (kernel (n • 𝟙 G)) k` is by definition the $k$-th sheaf cohomology group $H^k$ of this kernel sheaf on the fppf site of $S$, with its abelian group structure. The assertion is that every element $x$ of this group satisfies $n \cdot x = 0$; that is, $H^k\bigl(S_{\mathrm{fppf}}, G[n]\bigr)$ is annihilated by $n$ for all $k$ and all $G$.
--
--   This is the standard observation that the cohomology of an $n$-torsion sheaf is $n$-torsion, so that each $H^k(S_{\mathrm{fppf}}, G[n])$ is a module over $\mathbf Z/n$. It is used in the treatment of the Kummer-type exact rows attached to $n$-torsion on the fppf site, and is cited by [`AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul`](thm.html#AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_fppfCohomology_kernel_zsmul_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfCohomology_kernel_zsmul_eq_zero
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (k : ℕ)
    (x : fppfCohomology specInt (kernel (n • 𝟙 G)) k) : n • x = 0 := by sorry
