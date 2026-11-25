-- Prove2me | Theorems.Thm_FiniteEnergyPlane_disk_riemannHilbert_estimate
-- name    : FiniteEnergyPlane.disk_riemannHilbert_estimate
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:34:16.583085+00:00
-- url     : https://prove2.me/theorems/2702932e-a0d3-5a55-a129-cad847d106f7
-- title:
--   The $L^p$ estimate up to the boundary for real-line boundary values
-- statement:
--   The a priori estimate for the Cauchy–Riemann operator on the closed unit disk $D$ with boundary values in a loop of real lines.
--
--   Let $1<p<\infty$ and let $\varphi:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a smooth $1$-periodic loop. There is a constant $C\ge0$ such that every $w\in C^1(D,\mathbb{C})$ with $w(e^{2\pi it})\in\mathbb{R}\,\varphi(t)$ for all $t$ satisfies
--   $$\|Dw\|_{L^p(D)}\le C\big(\|\partial_sw+i\,\partial_tw\|_{L^p(D)}+\|w\|_{L^p(D)}\big).$$
--
--   The estimate is uniform in $w$ and holds for every winding number of $\varphi$; it extends to the operator with a bounded zeroth-order term.
--
--   **Formalization Note** Norms are `eLpNorm` on the open disk, with values in $[0,\infty]$. That $\varphi$ is a loop avoiding $0$ is expressed by `HasLoopWind φ k` for some integer $k$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 12 and Proposition 16

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorem 12 and Proposition 16 (the `L^p` estimate up to the boundary, `1 < p < ∞`). Let
`φ` be a smooth loop in `ℂ \ {0}`. There is a constant `C` such that every `C¹` function `w` on the closed unit
disk with `w(e^{2πit}) ∈ ℝ φ(t)` satisfies
`‖Dw‖_{L^p(D)} ≤ C (‖∂ₛw + i ∂ₜw‖_{L^p(D)} + ‖w‖_{L^p(D)})`. -/
theorem disk_riemannHilbert_estimate (p : ℝ) (hp : 1 < p) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (k : ℤ) (hk : HasLoopWind φ k) :
    ∃ C : ℝ≥0, ∀ w : ℂ → ℂ, ContDiffOn ℝ 1 w (closedBall 0 1) →
      (∀ t : ℝ, ∃ r : ℝ, w (ccwLoop 1 t) = r • φ t) →
      eLpNorm (fun z => fderiv ℝ w z) (ENNReal.ofReal p) (volume.restrict (ball 0 1)) ≤
        C * (eLpNorm (fun z => ds w z + Complex.I * dt w z) (ENNReal.ofReal p)
            (volume.restrict (ball 0 1)) +
          eLpNorm w (ENNReal.ofReal p) (volume.restrict (ball 0 1))) := by
  sorry

end FiniteEnergyPlane
