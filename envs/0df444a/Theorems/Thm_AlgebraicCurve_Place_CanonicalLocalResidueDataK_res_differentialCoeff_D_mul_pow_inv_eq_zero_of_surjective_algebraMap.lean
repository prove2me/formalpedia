-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
-- name    : AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/83fff992-553d-57f8-b5f0-b20684ad36d6
-- title:
--   Vanishing residue of partialᵥ(dt) t⁻⁽ⁿ⁺¹⁾ at a rational place
-- statement:
--   Let $K\subseteq F$ be fields, $F$ a $K$-algebra, and let $v$ be a place of $F$ over $K$, that is a valuation subring $\mathcal O_v\subseteq F$ containing the image of $K$, different from $F$, and a principal ideal ring. Assume the distinguished element $\pi_v$ chosen as an irreducible of $\mathcal O_v$ has the property that $D_{F/K}(\pi_v)$ spans $\Omega_{F/K}$ over $F$, and that $\Omega_{F/K}$ is nontrivial; write $\partial_v(\omega)$ for the coefficient of $\omega$ against $D_{F/K}(\pi_v)$ (that is, the $f$ with $\omega = f\cdot D_{F/K}(\pi_v)$, and $0$ if none exists). Assume moreover that $K\to\mathcal O_v/\mathfrak m_v$ is surjective, and that $\partial_v(D_{F/K}(h))\in\mathcal O_v$ for every $h\in\mathcal O_v$. Let $R$ consist of a $K$-linear map $\mathrm{res}\colon F\to \mathcal O_v/\mathfrak m_v$ vanishing on $\mathcal O_v$, satisfying $\mathrm{res}(f)=\overline{\pi_v f}$ whenever $\pi_v f\in\mathcal O_v$, and $\mathrm{res}(\pi_v^{-(n+1)})=0$ for all $n\ge 1$. Then for every $t\in F$ with $\mathrm{ord}_v(t)=1$ and every integer $n\ge 1$,
--   $$\mathrm{res}\bigl(\partial_v(D_{F/K}(t))\cdot t^{-(n+1)}\bigr)=0.$$
--
--   This is the higher-pole half of the coordinate independence of the local residue at a place with residue field $K$: it shows that the residue datum attached to the chosen uniformizer $\pi_v$ kills the monomials $t^{-(n+1)}\,dt$ for any other uniformizer $t$. It is used in the comparison of the residue with the $t^{-1}$-Laurent coefficient of a differential and, through that, in the computations of residues of $X$-power differentials at the finite and infinite places of a rational function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean

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

theorem AlgebraicCurve.Place.CanonicalLocalResidueDataK.res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (R : v.CanonicalLocalResidueDataK) {t : F} (ht : v.ord t = 1) {n : ℕ} (hn : 1 ≤ n) :
    R.res (v.differentialCoeff (KaehlerDifferential.D K F t) * (t ^ (n + 1))⁻¹) = 0 := by sorry
