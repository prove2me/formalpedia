-- Prove2me | Theorems.Thm_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
-- name    : AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/e5eccca5-28db-5e4e-bd71-baa87ac59a8f
-- title:
--   Residue term vanishes for a differential regular at v
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and suppose $F/K$ carries canonical local residue data in the starred sense: for every place $v$ a distinguished datum `CanonicalLocalResidueDataK`, consisting of local residue data together with the vanishing of the residue on $(\pi_v^{n+1})^{-1}$ for all $n \ge 1$, whose underlying $K$-linear map $F \to \kappa(v)$ is `Place.localResidue`. Here a place $v$ of $F/K$ is a valuation subring $\mathcal{O}_v \subseteq F$ which contains $\operatorname{algebraMap} K F(a)$ for all $a \in K$, is not all of $F$, and is a principal ideal ring, and $\kappa(v)$ denotes its residue field. Fix such a $v$, assume that $d\pi_v := D_{K,F}(\pi_v)$ for the chosen uniformizer $\pi_v$ spans $\Omega_{F/K}$ as an $F$-module, and that $\Omega_{F/K}$ is nontrivial. Let $\omega \in \Omega_{F/K}$ and $f \in F$ with $f \in \mathcal{O}_v$ and $\omega = f \cdot d\pi_v$, and let $g \in F$ with $g \in \mathcal{O}_v$. Then the $v$-th Kähler residue term of $\omega$ against the constant family `diagonalHom K F g` (the family taking value $g$ at every place) vanishes: $\operatorname{Tr}_{\kappa(v)/K}\bigl(\operatorname{res}_v(g \cdot c_v(\omega))\bigr) = 0$, where $c_v(\omega)$ is the coefficient of $\omega$ with respect to $d\pi_v$ (chosen if it exists, and $0$ otherwise).
--
--   This is the local vanishing statement that a differential regular at $v$ has zero residue pairing against functions regular at $v$, in the form used for the residue terms indexed by places. It is the per-place input to the verification that the residue sum annihilates coboundaries in the two-chart setting, where it is cited by [`AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter`](thm.html#AlgebraicGeometry.Scheme.TwoAffineOpenCover.residuesVanishOnCoboundaries_of_isSectional_of_isCompletionAlong_of_hasParameter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.kaehlerResidueTerm_diagonalHom_eq_zero_of_eq_smul_dCoord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
    {v : Place K F} [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : f ∈ v.toValuationSubring) (hω : ω = f • v.dCoord)
    {g : F} (hg : g ∈ v.toValuationSubring) :
    kaehlerResidueTerm ω (diagonalHom K F g) v = 0 := by sorry
