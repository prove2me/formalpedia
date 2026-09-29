-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed
-- name    : AlgebraicCurve.residueTheoremK_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/0b4c7479-cbcc-5c87-9c16-80c7c5d57ccc
-- title:
--   Residue theorem over an algebraically closed base field
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field equipped with a $K$-algebra structure, subject to the following hypotheses. Geometric structure of $F/K$: every nonzero $\omega \in \Omega[F⁄K]$ admits a divisor $D$ on the places of $F/K$ with $D(v) = v.\mathrm{ordDifferential}\,\omega$ for all $v$ (`HasCanonicalDivisor`); for every place $w$ the element $w.\mathrm{dCoord}$ spans $\Omega[F⁄K]$ over $F$ (`DCoordGenerates`); every $f \neq 0$ in $F$ has a divisor of degree $0$ recording the orders $v.\mathrm{ord}\,f$ (`HasPrincipalDivisors`); each residue field $\kappa(v)$ is finite-dimensional over $K$; $\Omega[F⁄K]$ is nontrivial, and `IsCurveOver K F` holds, i.e. principal divisors exist, residue fields are finite over $K$, and $\Omega[F⁄K]$ is free of rank one over $F$. Local residues: each place of $F/K$ carries a local residue datum, and indeed `HasCanonicalLocalResidueKStar K F` provides a chosen family of canonical local residue data — $K$-linear maps $\mathrm{res}_v : F \to \kappa(v)$ vanishing on the valuation subring, sending $f$ with $\pi_v f$ integral to the residue class of $\pi_v f$, and annihilating $(\pi_v^{n+1})^{-1}$ for $n \geq 1$. Presentation over a rational function field: $F$ is an algebra over $\mathrm{RatFunc}\,K$, compatibly with $K$, integral, module-finite and separable over it, while $\mathrm{RatFunc}\,K$ itself satisfies the same curve package over $K$ (`IsCurveOver`, finite residue fields at all places, nontrivial $\Omega[\mathrm{RatFunc}\,K⁄K]$, and `DCoordGenerates` at every place). The conclusion is `ResidueTheoremK K F`: for every family $R$ assigning to each place $v$ of $F/K$ a canonical local residue datum, every nonzero $\omega \in \Omega[F⁄K]$ and every $f \in F$, the Weil functional $\mathrm{weilOfKaehlerK}\,R\,\omega$ vanishes on the diagonal adèle of $f$. Some hypotheses overlap: `IsCurveOver K F` already yields principal divisors and finiteness of the residue fields, and `HasCanonicalLocalResidueKStar K F` already yields `HasLocalResidue K F`.
--
--   This is the residue theorem for the function field $F/K$ in its canonical $K$-valued (Tate) form: the sum of the local residues of $f\,\omega$ over all places vanishes, expressed as the vanishing of the associated adelic Weil functional on the diagonal copy of $F$. It is the input for the duality step behind Riemann–Roch for function fields and for the construction of differentials with prescribed orders, and is used by [`AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed`](thm.html#AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed), [`AlgebraicCurve.residueTheorem_of_isAlgClosed`](thm.html#AlgebraicCurve.residueTheorem_of_isAlgClosed) and [`AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero`](thm.html#AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero); its proof reduces the general case to the rational function field by the trace compatibility of residues under the finite separable extension $F/\mathrm{RatFunc}\,K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheoremK K F := by sorry
