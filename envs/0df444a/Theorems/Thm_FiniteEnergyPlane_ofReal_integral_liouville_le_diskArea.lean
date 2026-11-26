-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ofReal_integral_liouville_le_diskArea
-- name    : FiniteEnergyPlane.ofReal_integral_liouville_le_diskArea
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T20:43:11.486254+00:00
-- url     : https://prove2.me/theorems/c5a21fab-601d-58e9-9825-7b027fa01e6a
-- title:
--   Action of a loop transverse to a radial characteristic foliation is bounded by the disk area
-- statement:
--   Let $e : \mathbb{C} \to \mathbb{R}^4$ be smooth, let $\lambda_0 = \tfrac12 \sum_k (q_k\,dp_k - p_k\,dq_k)$ be the Liouville form and $\omega_0 = d\lambda_0$, and write $z = s + it$. The characteristic field of $e$ is the vector field $V$ on the parameter plane determined by $(ds \wedge dt)(V, w) = (e^*\lambda_0)(w)$ for all $w$, that is $V = \lambda_0(\partial_t e) - i\,\lambda_0(\partial_s e)$. Assume:
--
--   1. $V(z_0) = 0$ for a point $z_0$ of the open unit disk $D$;
--   2. every characteristic leaf of the closed unit disk $\bar D$ issues from $z_0$ and reaches the unit circle: through every $z \in \bar D \setminus \{z_0\}$ there is an integral curve $\sigma$ of $V$ on $(-\infty, b]$, $b \ge 0$, with $\sigma(0) = z$, $\sigma(\tau) \to z_0$ as $\tau \to -\infty$, $\sigma(\tau) \in D$ for $\tau < b$ and $|\sigma(b)| = 1$;
--   3. $(e^*\lambda_0)_z(iz) > 0$ at every point $z$ of the unit circle.
--
--   Let $c : \mathbb{R} \to \bar D$ be a $C^1$ loop of period $1$ that winds once around $z_0$ and is transverse to the characteristic foliation, i.e. $(e^*\lambda_0)_{c(t)}(c'(t)) \neq 0$ for all $t$. Then
--   $$\int_0^1 (e^*\lambda_0)_{c(t)}\big(c'(t)\big)\, dt \;\le\; \int_D \max\big(\omega_0(\partial_s e, \partial_t e), 0\big)\, ds\, dt .$$
--
--   Role: this is the planar part of the bound "action of the boundary loop $\le$ area of the spanning disk" for pseudoholomorphic disks with boundary on a special spanning disk (Hryniewicz 2014, Section 3.2; Hofer–Wysocki–Zehnder 1995, (26)–(27)), where $c$ is the boundary loop read in the parameter plane of the disk. It is stated for an arbitrary smooth $e$, so it applies to any disk whose characteristic foliation has this radial form.
--
--   Formalization Note: the left-hand side is `ENNReal.ofReal` of the interval integral of `liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t))` over $[0,1]$, and the right-hand side is `diskArea e`. The characteristic field is `charField e`, hypothesis 2 is `LeavesRadiateFrom e z₀`, and "winds once around $z_0$" is `HasLoopWind (fun t => c t - z₀) 1`, which also gives continuity and $1$-periodicity.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), Section 3.2; H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), (26)-(27)

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Action of a loop transverse to the characteristic foliation of a disk. Let `e : ℂ → V 1` be
smooth, and suppose its characteristic field vanishes at a point `z₀` of the open unit disk, every
characteristic leaf of the closed unit disk issues from `z₀` and reaches the unit circle, and
`e*λ₀` is positive on the counterclockwise tangent vector `i z` at every point `z` of the unit circle.
Let `c` be a `C¹` loop in the closed unit disk that winds once around `z₀` and is transverse to the
characteristic field, i.e. `e*λ₀(c'(t)) ≠ 0` for all `t`. Then the integral `∫₀¹ e*λ₀(c'(t)) dt` is at
most the positive part of the `dλ₀`-area of `e`. -/
theorem ofReal_integral_liouville_le_diskArea (e : ℂ → V 1) (he : ContDiff ℝ ∞ e) (z₀ : ℂ)
    (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hV : charField e z₀ = 0) (hL : LeavesRadiateFrom e z₀)
    (hS : ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z)))
    (c : ℝ → ℂ) (hc : ContDiff ℝ 1 c) (hcA : ∀ t, c t ∈ closedBall (0 : ℂ) 1)
    (hw : HasLoopWind (fun t => c t - z₀) 1)
    (htr : ∀ t, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t)) ≠ 0) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, liouville (e (c t)) (fderiv ℝ e (c t) (deriv c t))) ≤
      diskArea e := by
  sorry

end FiniteEnergyPlane
