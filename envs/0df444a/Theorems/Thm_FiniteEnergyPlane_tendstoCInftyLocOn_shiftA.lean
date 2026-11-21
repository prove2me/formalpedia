-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendstoCInftyLocOn_shiftA
-- name    : FiniteEnergyPlane.tendstoCInftyLocOn_shiftA
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T19:47:58.677815+00:00
-- url     : https://prove2.me/theorems/6c8d8035-d326-439e-a918-e804679b4958
-- title:
--   Translates of a smooth plane depend continuously on the shift in the C-infinity-loc topology
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ be $C^\infty$ and let $c_k\to c$ in $\mathbb{R}$. Then the translates $c_k\cdot u = e^{2c_k}u$ converge to $c\cdot u = e^{2c}u$ in $C^\infty_{\mathrm{loc}}$ on every subset $O\subset\mathbb{C}$: on each compact $K\subset O$, every derivative of order $m$ converges uniformly on $K$.
--
--   Role: continuity of the $\mathbb{R}$-action of the symplectization on smooth planes, in the form consumed by persistence statements for intersections.
--
--   **Formalization Note** The translation is `shiftA c u`, i.e. $z\mapsto e^{2c}u(z)$ (Hryniewicz 2012, Remark 3.10, with $\mathbb{R}\times S\cong\mathbb{R}^{2n+2}\setminus\{0\}$); convergence is `JHolomorphic.TendstoCInftyLocOn`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.22; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 2.3

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Translations in the `ℝ`-direction depend continuously on the shift in `C^∞_loc`: if `u` is
smooth and `cₖ → c`, then `shiftA cₖ u → shiftA c u` in `C^∞_loc` on every set `O ⊆ ℂ`. -/
theorem tendstoCInftyLocOn_shiftA {n : ℕ} (u : ℂ → V n) (hu : ContDiff ℝ ∞ u)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : Tendsto c atTop (𝓝 c₀)) (O : Set ℂ) :
    JHolomorphic.TendstoCInftyLocOn (fun k => shiftA (c k) u) (shiftA c₀ u) O := by
  sorry

end FiniteEnergyPlane
