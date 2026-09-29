-- Prove2me | Theorems.Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd
-- name    : FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/2a24797b-57eb-5317-893a-2197572f2ec0
-- title:
--   Unfolding an integral over a fundamental set into coset integrals
-- statement:
--   Let $\Gamma$ be a subgroup of $SL_2(\mathbb{Z})$ of finite index with $-1\in\Gamma$, let $E$ be a normed additive commutative group that is a normed space over $\mathbb{R}$, and let $f:\mathfrak{H}\to E$ be a function on the upper half-plane which is integrable, for the measure `volume` on $\mathfrak{H}$, on the set $\mathcal{F}_\Gamma=\bigcup_{q\in SL_2(\mathbb{Z})/\Gamma}\sigma_q^{-1}\cdot\mathcal{D}$, where $\mathcal{D}$ is Mathlib's closed standard fundamental domain `ModularGroup.fd` for the modular group, $\sigma_q=$`Quotient.out q` is the chosen representative of the coset $q$, and the action is the Möbius action of $SL_2(\mathbb{Z})$ on $\mathfrak{H}$; this union is the project's `gammaFundamentalSet`. The conclusion is the identity $$\int_{\mathcal{F}_\Gamma} f\,d\mathrm{vol}=\sum^{\mathrm{f}}_{q\in SL_2(\mathbb{Z})/\Gamma}\int_{\mathcal{D}} f(\sigma_q^{-1}\cdot\tau)\,d\mathrm{vol}(\tau),$$ the right-hand side being a `finsum` over the coset space, which by finiteness of the index is an ordinary finite sum. Note that the coset representatives entering both sides are the canonical choices `Quotient.out`, so no independence of the choice is asserted.
--
--   This is the standard unfolding of an integral over a fundamental set for a finite-index subgroup $\Gamma\le SL_2(\mathbb{Z})$ into a sum of integrals over the level-one fundamental domain, the basic device for computing hyperbolic integrals on modular curves. It is used for volume and limit computations on fundamental sets and for Petersson-type and $\bar\partial$-pairing integrals over the fundamental set of $\Gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular

theorem FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) (hf : IntegrableOn f (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ)) :
    ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ∫ τ in ModularGroup.fd, f ((Quotient.out q)⁻¹ • τ) := by sorry
