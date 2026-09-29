-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws
-- name    : AlgebraicCurve.Place.exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/0070efd3-c5d3-5cf6-996d-4ae605311377
-- title:
--   Cartier operator divides pole orders by p
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume the pair satisfies [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15), i.e. every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place is the order of $f$ there, every place of $F/K$ has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Let $p$ be a prime, assume $K$ has characteristic $p$ and is perfect, and let $x \in F$ be such that $F$ is finite-dimensional over the intermediate field $K(x)$. Let $C : \Omega_{F/K} \to \Omega_{F/K}$ be additive and satisfy Cartier's three laws: $C(f^p \cdot \omega) = f \cdot C\omega$ for all $f \in F$, $\omega \in \Omega_{F/K}$; $C(df) = 0$; and $C(f^{p-1} \cdot df) = df$ for all $f \in F$. Let $v$ be a place of $F/K$, that is, a valuation subring $\mathcal{O}_v \subsetneq F$ containing the image of $K$ and which is a principal ideal ring, with $\pi_v$ its chosen irreducible element and $\mathrm{dCoord}\,v = d\pi_v \in \Omega_{F/K}$, and let $\omega \in \Omega_{F/K}$. Then for every natural number $n$ and every $f \in F$ with $\omega = f \cdot d\pi_v$ and $\pi_v^{\,n} f \in \mathcal{O}_v$, there exists $g \in F$ with $C\omega = g \cdot d\pi_v$ and $\pi_v^{\,\lfloor (n+p-1)/p \rfloor} g \in \mathcal{O}_v$, the exponent being computed in natural-number arithmetic, so equal to $\lceil n/p \rceil$.
--
--   This is the local behaviour of the Cartier operator at a place: a pole of order at most $n$ in the coordinate $\pi_v$ is carried to a pole of order at most $\lceil n/p \rceil$ in the same coordinate, the cases $n = 0$ and $n = 1$ being the preservation of regularity and of simple poles. It is used in [`ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff`](thm.html#ModularCurve.isRegularAt_and_exists_eq_smul_dCoord_uniformizer_pow_mul_mem_of_isFrobPushDiff) to control the divisor of a differential obtained from a Frobenius-type construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_eq_smul_dCoord_and_uniformizer_pow_mul_mem_of_cartierLaws
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F] [AlgebraicCurve.IsCurveOver K F]
    (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (C : Ω[F⁄K] →+ Ω[F⁄K])
    (hC1 : ∀ (f : F) (ω : Ω[F⁄K]), C (f ^ p • ω) = f • C ω)
    (hC2 : ∀ f : F, C (KaehlerDifferential.D K F f) = 0)
    (hC3 : ∀ f : F, C (f ^ (p - 1) • KaehlerDifferential.D K F f) = KaehlerDifferential.D K F f)
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    ∀ (n : ℕ) (f : F), ω = f • v.dCoord → v.uniformizer ^ n * f ∈ v.toValuationSubring →
      ∃ g : F, C ω = g • v.dCoord ∧ v.uniformizer ^ ((n + p - 1) / p) * g ∈ v.toValuationSubring := by sorry
