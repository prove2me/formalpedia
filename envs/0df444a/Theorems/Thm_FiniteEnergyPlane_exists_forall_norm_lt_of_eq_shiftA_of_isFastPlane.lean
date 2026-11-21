-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T23:14:29.657933+00:00
-- url     : https://prove2.me/theorems/31f9dacc-1717-48ec-9f76-14c915cd031e
-- title:
--   Far intersections of two fast planes with translates
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit. Let $\tilde u,\tilde v:\mathbb{C}\to\mathbb{R}^4$ be fast finite-energy planes asymptotic to $P$ at $\infty$ whose $S$-components $\mathrm{proj}\circ\tilde u$, $\mathrm{proj}\circ\tilde v$ do not meet $x(\mathbb{R})$. For $\tau\in\mathbb{R}$ write $\tau\cdot\tilde v=e^{2\tau}\tilde v$ for the translate of $\tilde v$ in the $\mathbb{R}$-direction of the symplectization. Then there is $\tau_0\in\mathbb{R}$ such that for every $\varepsilon>0$ there is $R$ with
--   $$\tilde u(z)=(\tau\cdot\tilde v)(w),\ |\tau-\tau_0|\ge\varepsilon\ \Longrightarrow\ |z|<R\text{ and }|w|<R .$$
--
--   Role: intersections of $\tilde u$ with the translates of $\tilde v$ cannot escape to the puncture $\infty$, except possibly along translations converging to a single exceptional level $\tau_0$ (HWZ95, proof of Theorem 4.11, claims (56) and (68)).
--
--   **Formalization Note** $\tau\cdot\tilde v$ is `shiftA τ v`. The puncture at $\infty$ is `IsNondegenerateEnd H u cylInf P 1` (nondegenerate in the sense of Hryniewicz 2014, Definition 2.9; $P$ itself may be degenerate); "fast" is `IsFastPlane`. Neither plane is assumed embedded, and $\tilde u=\tilde v$ is allowed.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Lemma 6.23; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II, Geom. Funct. Anal. 5 (1995), 270–328, Theorem 4.11

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Two fast planes over the same orbit meet their translates only in a bounded region, away
from one exceptional translation. Let `u, v` be fast finite-energy planes asymptotic to the same
orbit `P` at `∞` whose `S`-components do not meet `x(ℝ)`. Then there is `τ₀ ∈ ℝ` such that for
every `ε > 0` there is `R` with: whenever `u z = (τ · v)(w)` (`τ · v = shiftA τ v`) and
`|τ - τ₀| ≥ ε`, both `‖z‖ < R` and `‖w‖ < R`. -/
theorem exists_forall_norm_lt_of_eq_shiftA_of_isFastPlane (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u v : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1)
    (hv : IsFastPlane H J v) (hvP : IsNondegenerateEnd H v cylInf P 1)
    (humiss : ∀ z, proj H (u z) ∉ Set.range P.x) (hvmiss : ∀ z, proj H (v z) ∉ Set.range P.x) :
    ∃ τ₀ : ℝ, ∀ ε > 0, ∃ R : ℝ, ∀ (τ : ℝ) (z w : ℂ), u z = shiftA τ v w → ε ≤ |τ - τ₀| →
      ‖z‖ < R ∧ ‖w‖ < R := by
  sorry

end FiniteEnergyPlane
