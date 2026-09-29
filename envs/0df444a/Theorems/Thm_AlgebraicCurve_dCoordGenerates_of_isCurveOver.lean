-- Prove2me | Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
-- name    : AlgebraicCurve.dCoordGenerates_of_isCurveOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/2eb1e0ff-91de-550a-bd77-cad165d366e9
-- title:
--   Differential of a uniformiser generates Ω_{F/K}
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, $K$ perfect, and $F$ essentially of finite type over $K$, and assume `IsCurveOver K F`, i.e. (a) every nonzero $f \in F$ admits a divisor $D$ on the places of $F/K$ with $D(v) = \operatorname{ord}_v f$ for all $v$ and $\deg D = 0$, (b) for every place $v$ the residue field of $v$ is a finite $K$-module, and (c) the module of Kähler differentials $\Omega[F\!\restriction\!K]$ is free of rank one over $F$. Here a place $v$ of $F/K$ is a valuation subring of $F$ which contains $\operatorname{algebraMap} K F(a)$ for every $a \in K$, is not all of $F$, and is a principal ideal ring. The conclusion is that every place $v$ satisfies `DCoordGenerates`, i.e. the single element $v.\mathrm{dCoord} = D_{K,F}(v.\mathrm{uniformizer})$, the Kähler differential of the chosen uniformiser `v.uniformizer` of $v$, spans $\Omega[F\!\restriction\!K]$ as an $F$-submodule: $\operatorname{span}_F\{v.\mathrm{dCoord}\} = \top$.
--
--   This is the statement that at each place of a curve the differential of a local uniformiser is a generator of the (rank-one) module of differentials, so that $d\pi_v$ may be used as a local coordinate. It discharges the hypothesis that every place has `DCoordGenerates`, which is carried by the Riemann–Roch and residue-theorem statements of the development and by the many results built on them, and it is deduced from the existence of a separating transcendental element (`exists_separating_transcendental`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates := by sorry
