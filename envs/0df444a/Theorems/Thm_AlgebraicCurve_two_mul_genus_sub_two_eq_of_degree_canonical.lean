-- Prove2me | Theorems.Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical
-- name    : AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/cfc83a00-2f84-5031-8bbd-e3a34ce04533
-- title:
--   Hurwitz genus formula for tame separable extensions
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields with compatible $K$-algebra structures (a scalar tower), $F'$ integral over $F$, finite-dimensional over $F$ and separable over $F$. Both $F$ and $F'$ are curves over $K$ in the sense of `IsCurveOver`: principal divisors exist (each nonzero element has a finitely supported divisor recording its orders at all places, of degree $0$), every residue field is finite over $K$, and the module of Kähler differentials is free of rank one; here a place is a valuation subring containing the image of $K$, proper and a principal ideal ring, $\deg v$ is the $K$-dimension of its residue field, and the degree of a divisor is $\sum_v D(v)\deg v$. At every place of $F$ and of $F'$ the differential $D(\text{uniformizer})$ spans the differentials (`DCoordGenerates`), and both levels satisfy `HasCanonicalDivisor`, so that for each nonzero $\omega$ a divisor $\mathrm{canonicalDivisorOf}$ with values $v.\mathrm{ordDifferential}\,\omega$ exists, and the genus is defined from the degree of such a divisor by $(\deg + 2)/2$. Assume: for each place $w$ of $F'$ and each nonzero $u$ with $\mathrm{ord}_w u = 0$, the coefficient of $D_{K}u$ with respect to $w$'s distinguished differential is zero or has nonnegative order at $w$; for each place $w$ of $F'$, the ramification index $e(w\mid F)$ — the least $n > 0$ of the form $\mathrm{ord}_w(\mathrm{algebraMap}\,f)$ for nonzero $f \in F$ — is nonzero in $F'$ (tameness). Assume further a nonzero $\omega_0 \in \Omega_{F/K}$ whose image in $\Omega_{F'/K}$ is nonzero, and that the associated canonical divisors have degrees $2g(K,F)-2$ and $2g(K,F')-2$ respectively. Then $$2g(K,F)' - 2 = [F':F]\,(2g(K,F)-2) + \sum_{w}\bigl(e(w\mid F)-1\bigr)\deg w,$$ the finitely supported sum being over all places $w$ of $F'$, with $g(K,F')$ on the left.
--
--   This is the Hurwitz genus formula for a finite separable extension of function fields with tame ramification, obtained from the differential (degree) form of the formula by inserting the Riemann–Roch identity $\deg K_X = 2g-2$ at both levels. It feeds the genus computations for the modular curves used later, among them [`AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq`](thm.html#AlgebraicCurve.finsum_ramificationIndexAlong_sub_one_eq) and the genus formulae for splitting fields; the local input on ramification degrees is the fundamental identity $\sum_{w \mid v} e(w\mid F) f(w\mid F) = [F':F]$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem two_mul_genus_sub_two_eq_of_degree_canonical {K : Type*} {F : Type*} {F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    [IsCurveOver K F] [∀ v : Place K F, v.DCoordGenerates] [IsCurveOver K F'] [∀ w : Place K F', w.DCoordGenerates]
    [HasCanonicalDivisor (K := K) (F := F)] [HasCanonicalDivisor (K := K) (F := F')]
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (hreg : ∀ (w : Place K F') (u : F'), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D K F' u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D K F' u)))
    (htame : ∀ w : Place K F', ((w.ramificationIndex F : ℕ) : F') ≠ 0)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (hω₀' : KaehlerDifferential.map K K F F' ω₀ ≠ 0)
    (hK : Divisor.degree (canonicalDivisorOf (K := K) hω₀) = 2 * (genus K F : ℤ) - 2)
    (hK' : Divisor.degree (canonicalDivisorOf (K := K) hω₀') = 2 * (genus K F' : ℤ) - 2) :
    2 * (genus K F' : ℤ) - 2
      = (Module.finrank F F' : ℤ) * (2 * (genus K F : ℤ) - 2)
        + ∑ᶠ w : Place K F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) := by sorry
