-- Prove2me | Theorems.Thm_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
-- name    : AlgebraicCurve.residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/171c6237-25d8-5b43-bf0e-33e2282b7162
-- title:
--   Residue theorem for F from K(x) via trace–residue commutation
-- statement:
--   Let $K$ be a perfect field and $F$ a field extension of $K$ which is also an algebra over the rational function field $\mathrm{RatFunc}\,K$, compatibly with $K$, with $F$ integral and module-finite, indeed separable, over $\mathrm{RatFunc}\,K$. Assume on both $F/K$ and $\mathrm{RatFunc}\,K/K$ the standing curve data: `HasCanonicalDivisor`, i.e. every nonzero Kähler differential has a finitely supported divisor whose value at each place $v$ is $v.\mathrm{ordDifferential}$ of it; `DCoordGenerates` at every place, i.e. the distinguished differential $v.\mathrm{dCoord}$ spans $\Omega$ over the field; nontriviality of the module of Kähler differentials; finiteness of every residue field over $K$; `IsCurveOver`, i.e. principal divisors exist and have degree $0$, residue fields are finite over $K$, and $\Omega$ is free of rank one; and `HasPrincipalDivisors` for $F$. Assume further (i) the residue theorem for $\mathrm{RatFunc}\,K$: for every nonzero $\omega\in\Omega[\mathrm{RatFunc}\,K/K]$ and every $f$, the associated Weil functional `weilOfKaehler` annihilates the diagonal adele of $f$; and (ii) `KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)`: for every place $v$ of $\mathrm{RatFunc}\,K$, every place $w$ of $F$ in the fibre of $v$, and every $g\in F$, the local term $\mathrm{Tr}_{\kappa(w)/K}\bigl(\mathrm{res}_w(g\cdot \text{coefficient of the pullback of } v.\mathrm{dCoord})\bigr)$ equals $\mathrm{Tr}_{\kappa(v)/K}$ of the completed local residue at $v$ of the completion trace of $g$ from $w$ to $v$. Then the residue theorem holds for $F$: for every nonzero $\omega\in\Omega[F/K]$ and every $f\in F$, the Weil functional attached to $\omega$ vanishes on the diagonal adele of $f$.
--
--   This is the inductive step of Tate's treatment of the residue theorem on a curve: the vanishing of the total residue of $f\,\omega$ over all places of $F$ is reduced to the same statement for the rational function field, the reduction being effected by the commutation of residues with traces through the local completions. It feeds [`AlgebraicCurve.residueTheorem_of_perfectField`](thm.html#AlgebraicCurve.residueTheorem_of_perfectField), where both hypotheses are discharged for separable $F/K(x)$ over a perfect $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute.lean

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
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_TateResidueCurrency
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute
    {K F : Type*} [Field K] [PerfectField K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := RatFunc K)]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    (hP1 : AlgebraicCurve.ResidueTheorem K (RatFunc K))
    (hRTCC : ModularCurve.KwF4R1V391a.KwF4R1V391aResidueTraceCompletionCommute K F (RatFunc K)) :
    AlgebraicCurve.ResidueTheorem K F := by sorry
