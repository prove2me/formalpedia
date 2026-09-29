-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one
-- name    : AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/f39d0826-64f3-5270-867e-68425c4d89d6
-- title:
--   Residue of dt/t is 1 at any uniformiser
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, i.e. a valuation subring $\mathcal O_v \subsetneq F$ containing the image of $K$ and whose ring structure is a principal ideal ring. Assume that the chosen differential $d\pi_v = D_{K/F}(\pi_v)$ of the selected uniformiser $\pi_v$ spans $\Omega_{F/K}$ as an $F$-module and that $\Omega_{F/K}$ is nontrivial, so that every $\omega$ has a well-defined coefficient $\partial_v(\omega) \in F$ with $\omega = \partial_v(\omega)\, d\pi_v$. Assume further the integrality hypothesis that $\partial_v(dh) \in \mathcal O_v$ for every $h \in \mathcal O_v$. Let $R$ be a canonical local residue datum at $v$: a $K$-linear map $\operatorname{res} \colon F \to \kappa(v)$ into the residue field of $\mathcal O_v$ which vanishes on $\mathcal O_v$, which satisfies $\operatorname{res}(f) = \overline{\pi_v f}$ whenever $\pi_v f \in \mathcal O_v$, and which kills $(\pi_v^{n+1})^{-1}$ for all $n \ge 1$. Then for every $t \in F$ with $\operatorname{ord}_v(t) = 1$ one has $\operatorname{res}\bigl(\partial_v(dt)\, t^{-1}\bigr) = 1$ in $\kappa(v)$.
--
--   This is the simple-pole half of the invariance of the local residue under a change of uniformiser: the logarithmic differential $dt/t$ has residue $1$ at $v$ for every element $t$ of valuation exactly one, not merely for the distinguished uniformiser $\pi_v$. It is used in identifying the coefficient of $\pi_v^{-1}$ in a Laurent-type expansion with the local residue of a differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_inv_eq_one.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_inv_eq_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {t : F} (ht : v.ord t = 1) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F t) * t⁻¹) = 1 := by sorry
