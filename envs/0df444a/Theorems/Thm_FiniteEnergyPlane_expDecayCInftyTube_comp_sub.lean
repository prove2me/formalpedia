-- Prove2me | Theorems.Thm_FiniteEnergyPlane_expDecayCInftyTube_comp_sub
-- name    : FiniteEnergyPlane.expDecayCInftyTube_comp_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-15T17:35:37.111196+00:00
-- url     : https://prove2.me/theorems/fc408f7b-96b6-4b3e-b398-e5e034c2b8a2
-- title:
--   Exponential C-infinity decay on a tube is preserved by composition with a map smooth near the limit
-- statement:
--   Let $E$ be a finite-dimensional and $F$ a complete real normed space, $U\subset E$ open and $G:U\to F$ smooth. Let $\rho,b>0$, let $g:\mathbb R\times\mathbb C\to E$ be smooth on $\mathbb R\times B_{2\rho}$, $1$-periodic in its first variable, with $g(t,w)\in U$ whenever $|w|\le\rho$, and let $f:\mathbb R\times\mathbb R\times\mathbb C\to E$ be such that $f(s,t,w)-g(t,w)$ decays like $e^{-bs}$ in $C^\infty$ as $s\to+\infty$, uniformly in $t\in\mathbb R$ and $w\in B_\rho$ (smooth on some $(s_0,\infty)\times\mathbb R\times B_\rho$, and every derivative of order $m$ bounded by $C_me^{-bs}$ for large $s$). Then $G(f(s,t,w))-G(g(t,w))$ decays like $e^{-bs}$ in $C^\infty$ in the same sense.
--
--   This is the tube version (with a transverse parameter $w$) of the composition rule for exponentially decaying maps on a cylindrical end, used to pass decay through nonlinear expressions such as almost complex structures and coordinates along a tube.
--
--   Formalization Note: decay on the tube is `ExpDecayCInftyTube h ρ b`, which bounds the full derivatives in $(s,t,w)$.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_Tube

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Exponential `C^∞` decay on a tube is preserved under composition with a map that is smooth
near the limit. Let `g(t, w)` be smooth and `1`-periodic in `t` on `ℝ × ball 0 (2ρ)`, with values
in an open set `U` for `|w| ≤ ρ`, let `G` be smooth on `U`, and let `f(s, t, w) - g(t, w)` decay
like `e^{-bs}` in `C^∞`, uniformly in `t` and `w ∈ ball 0 ρ`. Then `G(f(s, t, w)) - G(g(t, w))`
decays like `e^{-bs}` in `C^∞`, uniformly in `t` and `w ∈ ball 0 ρ`. -/
theorem expDecayCInftyTube_comp_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : E → F) (U : Set E) (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U)
    (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (g : ℝ × ℂ → E) (hg : ContDiffOn ℝ ∞ g (Set.univ ×ˢ ball (0 : ℂ) (2 * ρ)))
    (hgper : ∀ (t : ℝ) (w : ℂ), g (t + 1, w) = g (t, w))
    (hgU : ∀ (t : ℝ) (w : ℂ), w ∈ closedBall (0 : ℂ) ρ → g (t, w) ∈ U)
    (f : ℝ × ℝ × ℂ → E)
    (hf : ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => f q - g (q.2.1, q.2.2)) ρ b) :
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => G (f q) - G (g (q.2.1, q.2.2))) ρ b := by
  sorry

end FiniteEnergyPlane
