-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_regularDiffs_iff
-- name    : AlgebraicCurve.mem_regularDiffs_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/c78e2722-9ac8-5fec-a22e-e8e1fc265734
-- title:
--   Regular differentials already form a K-subspace
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ of characteristic zero, and let $x \in F$ be an element such that $F$ is algebraic over the intermediate field $K(x)$ obtained by adjoining $x$ to $K$ inside $F$; thus $F$ is a function field of one variable over $K$, presented by the chosen generator $x$. Here a place of $F/K$ is a valuation subring $\mathcal{O}_v \subseteq F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring; for such a $v$ and a Kähler differential $\omega \in \Omega[F\!/\!K]$ the order $\operatorname{ordDiff}_v(\omega) \in \mathbb{Z}$ is the valuation $v.\mathrm{ord}$ of the coefficient $\mathrm{diffCoeff}$ of $\omega$ with respect to the differential of the chosen uniformiser of $v$, and [`AlgebraicCurve.IsRegularDiff K F ω`](def/AlgebraicCurve_Differentials.html#L48) asserts $0 \le \operatorname{ordDiff}_v(\omega)$ for every place $v$ of $F/K$. The submodule [`AlgebraicCurve.regularDiffs K F`](def/AlgebraicCurve_Differentials.html#L56) is by definition the $K$-span inside $\Omega[F\!/\!K]$ of the set of differentials satisfying this regularity condition. The theorem asserts, for every $\omega \in \Omega[F\!/\!K]$, that $\omega$ lies in [`AlgebraicCurve.regularDiffs K F`](def/AlgebraicCurve_Differentials.html#L56) if and only if $\omega$ is itself regular in the above sense: the span contains nothing beyond its generators.
--
--   The statement says that the regular (everywhere holomorphic) differentials of a characteristic-zero function field of one variable are closed under addition and under scalar multiplication by $K$, so that the $K$-space of regular differentials may be described interchangeably as a span or by the local conditions $\operatorname{ordDiff}_v \ge 0$. It is used on the modular-curve side, in the identifications of integrality conditions for differentials of the form $g \cdot \mathrm{d}t$ lying in the space of regular differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean

import Definitions.Def_AlgebraicCurve_Differentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.mem_regularDiffs_iff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (ω : Ω[F⁄K]) :
    ω ∈ AlgebraicCurve.regularDiffs K F ↔ AlgebraicCurve.IsRegularDiff K F ω := by sorry
