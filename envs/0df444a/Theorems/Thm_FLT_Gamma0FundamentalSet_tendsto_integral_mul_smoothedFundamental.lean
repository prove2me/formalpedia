-- Prove2me | Theorems.Thm_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental
-- name    : FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/03800504-07ca-545c-aa23-72e89054fad6
-- title:
--   Planar integrals against the smoothed fundamental function
-- statement:
--   Let $\Gamma$ be a subgroup of $SL_2(\mathbb Z)$ of finite index containing $-1$, and let $P:\mathfrak H\to\mathbb C$ be a function with $P(\gamma\cdot\tau)=P(\tau)$ for all $\gamma\in\Gamma$ and all $\tau\in\mathfrak H$, almost everywhere strongly measurable for `volume` on $\mathfrak H$ and integrable on the set $\mathcal F_\Gamma=\bigcup_{q\in SL_2(\mathbb Z)/\Gamma}(\text{out}\,q)^{-1}\cdot\mathcal D$, the union over the cosets $q$ of the images of the standard fundamental domain $\mathcal D$ for $SL_2(\mathbb Z)$ under the inverses of the chosen representatives $\text{out}\,q$. For $T\in\mathbb R$ write $h_{\Gamma,T}=$ [`ModularCurve.smoothedFundamental`](def/ModularCurve_SmoothedFundamental.html#L170) $\Gamma\,T$, the real-valued function on $\mathbb C$ given by the finite sum over $q\in SL_2(\mathbb Z)/\Gamma$ of $\mathrm{puCut}_T$ (the product of the two cut-off factors `pu` and `gcut` at parameter $T$) evaluated at the Möbius image $\mathrm{num}(\text{out}\,q,z)/\mathrm{denom}(\text{out}\,q,z)$. The assertion is that, as $T\to\infty$,
--   $$\int_{\mathbb C}P(\mathrm{ofComplex}\,z)\,\bigl((\operatorname{Im}z)^{-2}\,h_{\Gamma,T}(z)\bigr)\,dz\ \longrightarrow\ \tfrac12\int_{\mathcal F_\Gamma}P(\tau)\,d\tau,$$
--   the integral on the left being taken over $\mathbb C$ with respect to Lebesgue measure, with the real weight $(\operatorname{Im}z)^{-2}h_{\Gamma,T}(z)$ viewed in $\mathbb C$, and $\mathrm{ofComplex}$ the map $\mathbb C\to\mathfrak H$ which is the identity on points of positive imaginary part.
--
--   This is the unfolding step for the smoothed fundamental function: the planar integral of a $\Gamma$-invariant weight against $h_{\Gamma,T}$ converges to half the integral over the fundamental set, the factor $\tfrac12$ coming from $-1\in\Gamma$ acting trivially on $\mathfrak H$. It supplies the Petersson-type term in the results on winding pairings and on periods modulo the period lattice that cite it, and it uses the properties of $h_{\Gamma,T}$ collected in [`ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one`](thm.html#ModularCurve.contDiff_and_finsum_smoothedFundamental_eq_one) together with the coset decomposition of the integral over the fundamental set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_ModularCurve_SmoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
        ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) := by sorry
