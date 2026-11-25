-- Prove2me | Theorems.Thm_FiniteEnergyPlane_disk_riemannHilbert_solvable
-- name    : FiniteEnergyPlane.disk_riemannHilbert_solvable
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-25T20:33:46.27181+00:00
-- url     : https://prove2.me/theorems/79ec4e72-d0af-5d20-8c77-da58d56f17db
-- title:
--   The linear Riemann–Hilbert problem on the disk
-- statement:
--   The boundary value problem for a linear Cauchy–Riemann operator on the closed unit disk $D$ with values on the boundary in a loop of real lines.
--
--   Let $A$ be a smooth map from $D$ to the real-linear endomorphisms of $\mathbb{C}$, and let $\varphi:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ be a smooth $1$-periodic loop of winding number $k\ge0$. For $f:D\to\mathbb{C}$, a solution for $f$ is a smooth $w:D\to\mathbb{C}$ with
--   $$\partial_sw+i\,\partial_tw+A\,w=f\ \text{ in the interior},\qquad w(e^{2\pi it})\in\mathbb{R}\,\varphi(t)\ \text{ for all }t .$$
--
--   1. For every smooth $f$ there is a solution.
--   2. The solutions for $f=0$ form a real vector space of functions on $D$ of dimension $2k+1$.
--   3. If $k=0$, a solution for $f=0$ that vanishes at some point of $D$ vanishes identically on $D$.
--
--   The numbers in 2 are those of the index of the problem, whose operator is onto; the statement is the linear theory of embedded pseudoholomorphic disks with totally real boundary.
--
--   **Formalization Note** Smoothness on $D$ is `ContDiffOn` on the closed ball, the winding number is `HasLoopWind`, and 2 asserts a list of $2k+1$ solutions such that every solution agrees on $D$ with exactly one real combination. The source states winding number $1$ and $0$; the form given here has every $k\ge0$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Theorem 12, Theorem 15 and Proposition 16

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal Real

/-- Hofer (1993), Theorems 12 and 15. Let `φ` be a smooth loop in `ℂ \ {0}` with winding number `k ≥ 0`
and `A` a smooth real-linear zeroth-order term on the closed unit disk `D`. Consider
`∂ₛw + i ∂ₜw + A w = f` on `D` with the boundary condition `w(e^{2πit}) ∈ ℝ φ(t)`.
(1) For every smooth `f` on `D` there is a smooth solution `w`.
(2) The smooth solutions with `f = 0` form a real vector space (of functions on `D`) of dimension `2k + 1`.
(3) If `k = 0`, a solution with `f = 0` that has a zero in `D` vanishes identically on `D`. -/
theorem disk_riemannHilbert_solvable (A : ℂ → ℂ →L[ℝ] ℂ) (hA : ContDiffOn ℝ ∞ A (closedBall 0 1))
    (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (k : ℕ) (hk : HasLoopWind φ k) :
    let Sol : (ℂ → ℂ) → (ℂ → ℂ) → Prop := fun f w =>
      ContDiffOn ℝ ∞ w (closedBall 0 1) ∧
      (∀ z ∈ ball (0 : ℂ) 1, ds w z + Complex.I * dt w z + A z (w z) = f z) ∧
      ∀ t : ℝ, ∃ r : ℝ, w (ccwLoop 1 t) = r • φ t
    (∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f (closedBall 0 1) → ∃ w, Sol f w) ∧
      (∃ b : Fin (2 * k + 1) → ℂ → ℂ, (∀ i, Sol 0 (b i)) ∧ ∀ w, Sol 0 w →
        ∃! a : Fin (2 * k + 1) → ℝ, ∀ z ∈ closedBall (0 : ℂ) 1, w z = ∑ i, a i • b i z) ∧
      (k = 0 → ∀ w, Sol 0 w → (∃ z ∈ closedBall (0 : ℂ) 1, w z = 0) →
        ∀ z ∈ closedBall (0 : ℂ) 1, w z = 0) := by
  sorry

end FiniteEnergyPlane
