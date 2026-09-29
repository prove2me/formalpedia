-- Prove2me | Theorems.Thm_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws
-- name    : AlgebraicCurve.kw_cart_C_eq_of_cartierLaws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/5f07bd99-8fb7-5736-a541-b1c2b2eb3397
-- title:
--   Coordinate Cartier operator agrees with any operator satisfying the Cartier laws
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra satisfying [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e. every nonzero $f\in F$ admits a divisor of degree $0$ recording its orders at all places of $F/K$, every place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank one over $F$. Let $p$ be a prime, let $K$ have characteristic $p$ and be perfect, let $F$ have characteristic $p$, and let $x\in F$ be such that $F$ is finite-dimensional over $K(x)$. Let $t\in F$ satisfy: $dt=\mathrm{D}_{K,F}(t)\neq 0$, the $F$-span of $\{dt\}$ is all of $\Omega_{F/K}$, every $y\in F$ is separable over the subfield underlying $F^{p}(t)$ (the adjunction of $t$ to the image subfield $F^p$ of the Frobenius), and the minimal polynomial of $t$ over $F^{p}$ has degree $p$. Let $C\colon\Omega_{F/K}\to\Omega_{F/K}$ be an additive map with $C(f^{p}\omega)=f\,C(\omega)$, $C(df)=0$ and $C(f^{p-1}df)=df$ for all $f\in F$. Then for every $\omega\in\Omega_{F/K}$ the coordinate operator `kw_cart_C`, which sends $\omega$ to $c\cdot dt$ where $c^{p}$ is the $(p-1)$-st coefficient in the chosen expansion over $F^{p}$ in powers of $t$ of the $dt$-coordinate of $\omega$, agrees with $C$ at $\omega$.
--
--   This is the uniqueness of the Cartier operation on the differentials of a one-variable function field over a perfect field, in the form identifying the concretely defined operator attached to a separating coordinate $t$ with any operator obeying the three Cartier laws. It is used to transport coordinate computations, in particular the $q$-expansion identities [`ModularCurve.coeff_qExpansionDiffAlong_cartier_pow`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_cartier_pow) and [`ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws`](thm.html#ModularCurve.coeff_qExpansionDiffAlong_pow_eq_coeff_mul_of_cartierLaws), to any operator given axiomatically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_kw_cart_C_eq_of_cartierLaws.lean

import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve.KwCart AlgebraicCurve.KwPke

theorem AlgebraicCurve.kw_cart_C_eq_of_cartierLaws {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K] [CharP F p]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ y : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield y)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hsemi : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hlog : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (ω : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg ω = C ω := by sorry
