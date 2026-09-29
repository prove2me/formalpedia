-- Prove2me | Theorems.Thm_AlgebraicCurve_genus_eq_genusFF
-- name    : AlgebraicCurve.genus_eq_genusFF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/35ea4d8e-84ab-5bbb-a01c-f993cbf6ce66
-- title:
--   Canonical-degree genus equals the adelic genus dim_K H¹(0)
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume $F/K$ is a curve in the project's sense, i.e. `IsCurveOver K F`: every nonzero $f \in F$ has a divisor $D$ with $D(v) = v.\mathrm{ord}(f)$ at every place $v$ and $\deg D = 0$, every residue field $v.\mathrm{ResidueField}$ is finite-dimensional over $K$, and $\Omega[F/K]$ is free of rank one over $F$. Assume further `HasCanonicalDivisor`, that every nonzero $\omega \in \Omega[F/K]$ admits a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}(\omega)$, and that for each place $v$ the element $v.\mathrm{dCoord}$ spans $\Omega[F/K]$ over $F$. Three further hypotheses are assumed: `FunctionFieldRiemannRoch`, that $\ell(D) - \ell(K_\omega - D) = \deg D + 1 - g$ for every nonzero $\omega$ (with $K_\omega$ the associated canonical divisor) and every divisor $D$; `WeilDualityAdelic`, that the index of specialty $i(D)$, defined as the $K$-dimension of the adele space modulo the sum of the bounded-adeles subspace of $D$ and the image of $F$, equals $\ell(K_\omega - D)$; and `ConstantsAreBase`, that the Riemann–Roch space of the zero divisor is exactly $K \cdot 1 \subseteq F$. The conclusion is that `genus K F`, namely $(\deg K_\omega + 2)/2$ for a classically chosen nonzero differential, equals `genusFF K F`, namely $\dim_K H^1(0)$.
--
--   This reconciles the two definitions of the genus of a one-variable function field: the one read off from the degree of a canonical divisor and the adelic one, $\dim_K \mathbb{A}_F/(\mathbb{A}_F(0) + F)$. It is the bridge used by the downstream results about $\mathrm{Pic}^0$ and its torsion, which are stated in terms of `genusFF`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_genus_eq_genusFF.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.genus_eq_genusFF
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F) (hWDA : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F := by sorry
