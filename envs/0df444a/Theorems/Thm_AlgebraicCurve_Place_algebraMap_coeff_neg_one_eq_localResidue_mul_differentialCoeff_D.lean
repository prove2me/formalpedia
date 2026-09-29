-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
-- name    : AlgebraicCurve.Place.algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/335c1452-c4db-5b4f-a92f-16598b6f3736
-- title:
--   Canonical residue as t⁻¹-coefficient of a Laurent expansion
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, equipped with a canonical local residue structure `HasCanonicalLocalResidueKStar K F`, which assigns to every place a distinguished set of local residue data whose residue map annihilates $(\pi_v^{n+1})^{-1}$ for all $n\ge 1$. Let $v$ be a place of $F$ over $K$, that is, a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring; assume the module $\Omega[F\,/\,K]$ of Kähler differentials is nontrivial and that $v$ satisfies `DCoordGenerates`, i.e. the differential $d\pi_v$ of the chosen uniformizer spans $\Omega[F\,/\,K]$ over $F$, so that every $\omega$ has a coefficient $\partial_v(\omega)\in F$ with $\omega=\partial_v(\omega)\cdot d\pi_v$ (taken $0$ if no such element exists). Assume further: the structure map $K\to\kappa(v)$ onto the residue field of the valuation subring is surjective; $\partial_v(dh)$ lies in the valuation subring whenever $h$ does; a ring homomorphism $\Lambda\colon F\to K(\!(t)\!)$ (Hahn series over $K$ with value group $\mathbb{Z}$) sends each constant $\mathrm{alg}_K(c)$ to the constant series $C(c)$ and satisfies $f\in\mathcal{O}_v$ if and only if $\Lambda f$ is a power series, i.e. lies in the image of `HahnSeries.ofPowerSeries`; and $t_0\in F$ satisfies $\Lambda t_0=t$, the series `HahnSeries.single 1 1`. Then for every $h\in F$ the image in $\kappa(v)$ of the coefficient of $t^{-1}$ in $\Lambda h$ equals $\operatorname{res}_v\bigl(h\cdot\partial_v(dt_0)\bigr)$, the value of the canonical local residue map at $h\,\partial_v(dt_0)$.
--
--   This is the local comparison between the canonical local residue attached to a place (defined through a chosen uniformizer and residue data) and the residue read off an explicit Laurent expansion realising that place, in the classical form stating that the residue of $h\,dt_0$ is the $t^{-1}$-coefficient of the expansion of $h$; it is the shape in which independence of the residue from the chosen coordinate is used. It is cited by [`TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm`](thm.html#TwoChartCech.Cover.LaurentChart.residue_eq_kaehlerResidueTerm), where residues on a two-chart cover are computed from Laurent expansions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.algebraMap_coeff_neg_one_eq_localResidue_mul_differentialCoeff_D
    {K F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    (v : AlgebraicCurve.Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (hint : ∀ h : F, h ∈ v.toValuationSubring →
      v.differentialCoeff (KaehlerDifferential.D K F h) ∈ v.toValuationSubring)
    (Λ : F →+* LaurentSeries K) (hΛC : ∀ c : K, Λ (algebraMap K F c) = HahnSeries.C c)
    (hΛv : ∀ f : F, f ∈ v.toValuationSubring ↔ Λ f ∈ (HahnSeries.ofPowerSeries ℤ K).range)
    {t₀ : F} (ht₀ : Λ t₀ = HahnSeries.single 1 1) (h : F) :
    algebraMap K v.ResidueField ((Λ h).coeff (-1)) =
      v.localResidue (h * v.differentialCoeff (KaehlerDifferential.D K F t₀)) := by sorry
