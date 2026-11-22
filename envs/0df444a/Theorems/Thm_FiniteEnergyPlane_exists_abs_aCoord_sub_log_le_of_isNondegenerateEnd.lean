-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-21T09:58:07.207484+00:00
-- url     : https://prove2.me/theorems/545ad231-0a3d-4ce1-ad51-acb381b95f6b
-- title:
--   Logarithmic growth of the R-coordinate at a positive puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ and let $\tilde u=(a,u):\mathbb{C}\to\mathbb{R}\times S$ (in the symplectization coordinates $y=e^{2a}\,\mathrm{pr}(y)$) be a map asymptotic at $\infty$ to the periodic Reeb orbit $P=(x,T)$, in the sense that $a(e^{2\pi(s+it)})-Ts-d_0\to0$ and $e^{bs}\,|u(e^{2\pi(s+it)})-x(Tt+c)|\to0$ uniformly in $t$ as $s\to+\infty$. Then there are $d\in\mathbb{R}$ and $R>0$ such that
--   $$\Big|a(\tilde u(z))-\frac{T}{2\pi}\log|z|-d\Big|\le1\qquad\text{for all }|z|\ge R.$$
--
--   Role: the $\mathbb{R}$-coordinate of a plane grows like $\frac{T}{2\pi}\log|z|$ at a positive puncture. This controls the growth of reparametrizations between planes with the same asymptotic orbit, as in Hryniewicz's Lemma 6.25.
--
--   **Formalization Note** The end hypothesis is `IsNondegenerateEnd H u cylInf P 1`, with `cylInf s t` $=e^{2\pi s}e^{2\pi i t}$. $a$ is `aCoord H` and $T$ is `P.T`. No smoothness, energy or holomorphicity of $u$ is assumed.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.25 (asymptotics as in Definition 2.9 of Hryniewicz 2014)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open Metric
open scoped Real

/-- Logarithmic growth of the `ℝ`-coordinate at a positive end: if `u` is asymptotic at `∞` to the
periodic Reeb orbit `P` of period `T` (in the sense of `IsNondegenerateEnd H u cylInf P 1`), then
there are `d` and `R > 0` with `|a(u(z)) - T log ‖z‖ / (2π) - d| ≤ 1` for all `‖z‖ ≥ R`. -/
theorem exists_abs_aCoord_sub_log_le_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ)
    (P : ReebOrbit H) (u : ℂ → V n) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ d R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ →
      |aCoord H (u z) - P.T * Real.log ‖z‖ / (2 * π) - d| ≤ 1 := by
  sorry

end FiniteEnergyPlane
