-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
-- name    : AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/316f8208-a64f-5962-b793-4cd0c95cd625
-- title:
--   Correspondence through an intermediate field scales by [F:E]
-- statement:
--   Let $K$, $F_0$, $E$, $F$ be fields, with $F_0$, $E$, $F$ algebras over $K$ and with $E$ and $F$ curves over $K$ in the sense of `IsCurveOver` (principal divisors exist, every place has residue field finite over $K$, and the module of Kähler differentials is free of rank one). Let $\varphi_0,\varphi_1 : F_0 \to F$ be $K$-algebra maps whose underlying ring homomorphisms are integral, let $\psi_0,\psi_1 : F_0 \to E$ be $K$-algebra maps whose underlying ring homomorphisms are integral, and let $\iota : E \to F$ be a $K$-algebra map which is integral, which makes $F$ a finite module over $E$ (`FiniteAlong`) and for which $F$ is separable over $E$ (`SeparableAlong`), both for the $E$-algebra structure on $F$ transported along $\iota$. Assume $\iota \circ \psi_0 = \varphi_0$ and $\iota \circ \psi_1 = \varphi_1$. Then for every divisor $D$ of $F_0$ over $K$, that is every finitely supported $\mathbb{Z}$-valued function on the places of $F_0$ over $K$, the divisor obtained by pulling $D$ back along $\varphi_0$ and pushing forward along $\varphi_1$ equals $\mathrm{finrankAlong}\,K\,\iota$, the $E$-rank of $F$ along $\iota$, times the divisor obtained by pulling $D$ back along $\psi_0$ and pushing forward along $\psi_1$.
--
--   This is the multiplicativity of a divisor correspondence under a factorisation of both legs through an intermediate curve: passing from $(\varphi_0,\varphi_1)$ to $(\psi_0,\psi_1)$ divides the correspondence by the degree $[F:E]$. It is used in the analysis of Hecke towers, where $E$ is a compositum of the images of the two legs and equality of correspondences is made to force this degree to be $1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
    {K F₀ E F : Type*} [Field K] [Field F₀] [Field E] [Field F]
    [Algebra K F₀] [Algebra K E] [Algebra K F] [IsCurveOver K E] [IsCurveOver K F]
    (φ₀ φ₁ : F₀ →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : F₀ →ₐ[K] E) (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (ι : E →ₐ[K] F) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hsep : SeparableAlong K ι)
    (h₀ : ι.comp ψ₀ = φ₀) (h₁ : ι.comp ψ₁ = φ₁) (D : Divisor K F₀) :
    Divisor.correspondence φ₀ φ₁ hφ₀ hφ₁ D = finrankAlong K ι • Divisor.correspondence ψ₀ ψ₁ hψ₀ hψ₁ D := by sorry
