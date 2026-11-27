-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_normalCoord_of_mem_range
-- name    : FiniteEnergyPlane.exists_normalCoord_of_mem_range
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T23:52:07.000161+00:00
-- url     : https://prove2.me/theorems/249b2420-54dc-58fb-bb27-c42716a58e53
-- title:
--   A complex normal coordinate for a trivial cylinder adapted to a spanning disk
-- statement:
--   Let $S = H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level with compatible complex structure $J$ on $\xi$, let $P = (x,T)$ be a prime periodic Reeb orbit and $e$ a special spanning disk for $P$, and let $p \in x(\mathbb{R})$. Then there are an open set $W \ni p$ of $\mathbb{R}^4\setminus\{0\}$, a smooth function $N: W\to\mathbb{C}$ and a constant $M$ such that:
--   - for $y\in W$, $N(y) = 0$ exactly when $y$ lies on the trivial cylinder $\mathbb{R}\times x(\mathbb{R})$, i.e. $\mathrm{proj}(y)\in x(\mathbb{R})$;
--   - $N$ is real at the points of $W$ that lie on the closed disk $e(\overline{\mathbb{D}})$;
--   - $N$ is $\tilde J$-complex linear to first order along the trivial cylinder: $\|dN(y)v + i\,dN(y)(\tilde J(y)v)\| \le M\,|N(y)|\,\|v\|$ for $y\in W$ and all $v$.
--
--   Role: a complex normal coordinate for the trivial cylinder over $P$ near a point of $P$, adapted to the spanning disk. Composed with a $\tilde J$-holomorphic curve it gives a complex function satisfying a Cauchy–Riemann type inequality, with real values along a boundary lying on the disk.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), Theorem 4.4 (boundary part); U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 3

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- A complex normal coordinate for the trivial cylinder `ℝ × x(ℝ)` adapted to a spanning disk. Let `e` be a
special spanning disk for the prime orbit `P = (x, T)` and `p ∈ x(ℝ)`. Then near `p` there is a smooth function
`N : V 1 → ℂ` on an open set `W ∋ p` (avoiding `0`) such that
* `N y = 0` exactly when `y ∈ ℝ × x(ℝ)`, i.e. `proj y ∈ x(ℝ)`;
* `N` is real on the points of `W` that lie on the closed disk `e(D)`;
* `N` is `J̃`-complex linear to first order along `ℝ × x(ℝ)`: `‖dN(y) v + i dN(y)(J̃(y) v)‖ ≤ M |N y| ‖v‖`
  for `y ∈ W`. -/
theorem exists_normalCoord_of_mem_range (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hP : P.IsPrime) (e : ℂ → V 1) (z₀ : ℂ)
    (he : IsSpecialSpanningDisk H P e z₀) (p : V 1) (hp : p ∈ Set.range P.x) :
    ∃ (W : Set (V 1)) (N : V 1 → ℂ) (M : ℝ), IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ ∞ N W ∧
      (∀ y ∈ W, y ≠ 0 ∧ (N y = 0 ↔ proj H y ∈ Set.range P.x)) ∧
      (∀ y ∈ W, y ∈ e '' closedBall 0 1 → (N y).im = 0) ∧
      ∀ y ∈ W, ∀ v : V 1,
        ‖fderiv ℝ N y v + Complex.I * fderiv ℝ N y (Jtilde H J y v)‖ ≤ M * ‖N y‖ * ‖v‖ := by
  sorry

end FiniteEnergyPlane
