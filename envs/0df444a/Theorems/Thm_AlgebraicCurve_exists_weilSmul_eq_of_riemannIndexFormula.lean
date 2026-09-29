-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_weilSmul_eq_of_riemannIndexFormula
-- name    : AlgebraicCurve.exists_weilSmul_eq_of_riemannIndexFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9ccf26ab-a0d0-5e57-944c-2b5a87636f05
-- title:
--   Weil differentials bounded by W are F-proportional
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, subject to the project's curve hypotheses: `IsCurveOver K F` (every nonzero $f \in F$ has a divisor $D$ with $D(v) = v.\mathrm{ord}\,f$ at every place and $\deg D = 0$; each residue field $v.\mathrm{ResidueField}$ is finite over $K$; and $\Omega[F/K]$ is free of rank one over $F$), `HasCanonicalDivisor` (every nonzero $\omega \in \Omega[F/K]$ has a divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}\,\omega$), and the existence of at least one place of $F/K$. Assume the Riemann index formula `RiemannIndexFormula K F`: for every divisor $D$ one has $i(D) = \ell(D) - (\deg D + 1 - g)$, where $i(D) =$ `indexOfSpecialty D` is the $K$-dimension of the quotient of the adèle space $\mathbb{A} = \bigsqcup_D$ `adeleBdd D` (sup over divisors of the spaces of families $\alpha$ with $v(\alpha_v) \le \exp(D(v))$ for all $v$) by the sum of `adeleBdd D` with the global subspace, $\ell$ is the project's Riemann–Roch dimension and $g$ is `genus K F`. Let $W$ be a divisor and let $\varphi, \mu$ be $K$-linear functionals on $\mathbb{A}$ lying in `omegaSpace W`, i.e. annihilating the sum of `adeleBdd W` and the global subspace, with $\varphi \ne 0$. Then there is $f \in F$ with $\mu =$ `weilSmul K F f φ`, that is, $\mu$ is the composite of $\varphi$ with multiplication by $f$ on the adèle space.
--
--   This is the existence half of the statement that the Weil differentials of $F/K$ form a one-dimensional $F$-vector space, in the form restricted to two Weil differentials bounded by one and the same divisor $W$; it is used to derive the unrestricted rank-one statement and, through that, enters the comparison of differentials on modular curves with Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_weilSmul_eq_of_riemannIndexFormula.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PoleDivisorPackage
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_RiemannRochRows

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem exists_weilSmul_eq_of_riemannIndexFormula {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by sorry
