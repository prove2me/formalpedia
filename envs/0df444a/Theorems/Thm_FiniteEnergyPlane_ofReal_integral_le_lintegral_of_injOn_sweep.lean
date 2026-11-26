-- Prove2me | Theorems.Thm_FiniteEnergyPlane_ofReal_integral_le_lintegral_of_injOn_sweep
-- name    : FiniteEnergyPlane.ofReal_integral_le_lintegral_of_injOn_sweep
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T21:32:12.564215+00:00
-- url     : https://prove2.me/theorems/c4621e16-01c3-4a76-9e32-5c55f9ecf06b
-- title:
--   Area bound for an injective sweep of a half-strip
-- statement:
--   Let $G : \mathbb{C} \to \mathbb{C}$ be differentiable with derivative $G'$, and let $J(p) = \operatorname{Re}(G'(p)1)\operatorname{Im}(G'(p)i) - \operatorname{Im}(G'(p)1)\operatorname{Re}(G'(p)i)$ be its Jacobian, assumed continuous. Let $f : \mathbb{C} \to \mathbb{R}$ be continuous. Assume:
--   - on the closed half-strip $\{\operatorname{Re} p \le 0,\ 0 \le \operatorname{Im} p \le 1\}$, $J$ is differentiable in the real direction with $\partial_{\operatorname{Re}} J = (f \circ G)\, J$;
--   - $J(it) > 0$ for $t \in [0,1]$;
--   - $G$ is injective on the half-strip $Q = \{\operatorname{Re} p < 0,\ 0 \le \operatorname{Im} p < 1\}$ and maps it into the open unit disk.
--
--   Then $$\mathrm{ofReal}\Big(\int_0^1 J(it)\,dt\Big) \le \int_{|z|<1} \max(f(z), 0)\, dz .$$
--
--   Role: the measure-theoretic half of an area bound for a loop swept along a flow: $G(\tau + it)$ is the image of the loop point $c(t)$ after time $\tau$.
-- source:
--   Elementary lemma in the setting of U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), § 3.2

import Mathlib

namespace FiniteEnergyPlane

open MeasureTheory Metric Set
open scoped ENNReal

/-- An area bound for an injective sweep of the half-strip. Let `G : ℂ → ℂ` be differentiable with
derivative `G'`, and let `J p = (G' p 1).re (G' p i).im - (G' p 1).im (G' p i).re` be its Jacobian,
assumed continuous. Suppose that on the closed half-strip `re ≤ 0, 0 ≤ im ≤ 1` the Jacobian
satisfies `∂_{re} J = (f ∘ G) J` for a continuous `f : ℂ → ℝ`, that `J` is positive on the segment
`[0, i]`, and that `G` is injective on the
half-strip `{re < 0, 0 ≤ im < 1}` and maps it into the open unit disk. Then the integral of `J` over
the segment `[0, i]` is at most `∫_{|z| < 1} max(f, 0)`. -/
theorem ofReal_integral_le_lintegral_of_injOn_sweep (G : ℂ → ℂ) (G' : ℂ → ℂ →L[ℝ] ℂ)
    (hG : ∀ p, HasFDerivAt G (G' p) p) (J : ℂ → ℝ)
    (hJ : ∀ p, J p = (G' p 1).re * (G' p Complex.I).im - (G' p 1).im * (G' p Complex.I).re)
    (hJc : Continuous J) (f : ℂ → ℝ) (hf : Continuous f)
    (hJd : ∀ p : ℂ, p.re ≤ 0 → p.im ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (fun τ : ℝ => J (τ + p.im * Complex.I)) (f (G p) * J p) p.re)
    (hJ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 < J (t * Complex.I))
    (hinj : InjOn G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1})
    (hmaps : MapsTo G {p : ℂ | p.re < 0 ∧ p.im ∈ Ico (0 : ℝ) 1} (ball 0 1)) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..1, J (t * Complex.I)) ≤
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (f z) := by
  sorry

end FiniteEnergyPlane
