-- Prove2me | Theorems.Thm_DbarRegularity_exists_memLp_tendsto_eLpNorm_sub
-- name    : DbarRegularity.exists_memLp_tendsto_eLpNorm_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T18:17:26.584956+00:00
-- url     : https://prove2.me/theorems/8e169cc3-b56e-4352-956e-83c1c77eaa4a
-- title:
--   An L^p-Cauchy family indexed by ε → 0⁺ converges in L^p
-- statement:
--   Let $(\alpha,\mu)$ be a measure space, $E$ a Banach space and $1\le p\le\infty$. Let $(u_\varepsilon)_{\varepsilon>0}$ be functions $\alpha\to E$ with $u_\varepsilon\in L^p(\mu)$ for every $\varepsilon>0$, and suppose that for every $\delta>0$ there is $\eta_0>0$ with $\|u_\varepsilon-u_\eta\|_p\le\delta$ whenever $0<\varepsilon,\eta<\eta_0$. Then there is $g\in L^p(\mu)$ with
--   $$\|u_\varepsilon-g\|_p\to0\qquad(\varepsilon\to0^+).$$
--
--   This is completeness of $L^p$ for families indexed by $\varepsilon\to0^+$.
--
--   **Formalization Note.** $p$ is in `ℝ≥0∞` with `[Fact (1 ≤ p)]`; the family is `u : ℝ → α → E` and its values at $\varepsilon\le0$ are ignored. The limit is along `𝓝[>] 0`, stated as `Tendsto (fun ε => eLpNorm (u ε - g) p μ) (𝓝[>] 0) (𝓝 0)`; the Cauchy condition is `eLpNorm (u ε - u η) p μ ≤ ENNReal.ofReal δ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Cauchy

namespace DbarRegularity

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Completeness of `L^p` along `ε → 0⁺`: a family `u ε ∈ L^p` (`ε > 0`) which is Cauchy in
`L^p` as `ε → 0⁺` converges in `L^p` to some `g ∈ L^p`. -/
theorem exists_memLp_tendsto_eLpNorm_sub {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [CompleteSpace E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : ℝ → α → E)
    (hu : ∀ ε : ℝ, 0 < ε → MemLp (u ε) p μ)
    (hc : ∀ δ : ℝ, 0 < δ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ ε η : ℝ, 0 < ε → ε < η₀ → 0 < η → η < η₀ →
      eLpNorm (u ε - u η) p μ ≤ ENNReal.ofReal δ) :
    ∃ g : α → E, MemLp g p μ ∧
      Tendsto (fun ε : ℝ => eLpNorm (u ε - g) p μ) (𝓝[>] 0) (𝓝 0) := by sorry

end DbarRegularity
