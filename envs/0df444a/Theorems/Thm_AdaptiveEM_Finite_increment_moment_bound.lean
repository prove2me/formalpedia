-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_increment_moment_bound
-- name    : AdaptiveEM.Finite.increment_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:45.010577+00:00
-- url     : https://prove2.me/theorems/e9a6d73b-c076-408c-9414-b3c5e597af36
-- title:
--   §6.2, bound after (41), p. 553 — E[‖X̂_s − X̄_s‖^{2p}] ≤ C³_{p,T} δ^p, uniformly in δ ∈ (0,1] and s ∈ [0,T]
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$, $(\mathcal F_t)$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$ be given. Let $f,g$ satisfy Assumption 4, let $h$ satisfy Assumption 2, let $T>0$, and let the family $h^\delta$, $0<\delta\le1$, satisfy Assumption 3 with each $h^\delta$ measurable. Write $\widehat X$ and $\overline X$ for the continuous and piecewise constant interpolants of the scheme (5) run with $h^\delta$ from $x_0$. For every $p\ge4$ there is a constant $C^3_{p,T}>0$ such that for all $\delta\in(0,1]$ and all $s\in[0,T]$
--   $$\mathbb E\big[\|\widehat X_s-\overline X_s\|^{2p}\big]\le C^3_{p,T}\,\delta^p .$$
--
--   Within a step the scheme moves by $f(\widehat X_{\underline s})(s-\underline s)+g(\widehat X_{\underline s})(W_s-W_{\underline s})$, and the steps of $h^\delta$ are at most $\delta T$; this bound turns that into the $\delta^{p}$ factor that yields the rate $\delta^{p/2}$ of Theorem 3.
--
--   **Formalization Note** The constant is chosen before $\delta$ and $s$. Measurability of each $h^\delta$ is an added regularity hypothesis (Assumption 3 states only the bounds (11)); it makes the scheme a family of random variables. The statement is for $p\ge4$, the range in which the paper's proof is given. The expectation is a $[0,\infty]$-valued integral.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 553, §6.2, proof of Theorem 3, (41) and the bound after it

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), §6.2, proof of Theorem 3, bound after (41), p. 553: under Assumption 4
and Assumption 3 with `h` satisfying Assumption 2, for every `p ≥ 4` there is `C³_{p,T} > 0`
with `E[‖X̂_s - X̄_s‖^{2p}] ≤ C³_{p,T} δ^p` for all `δ ∈ (0, 1]` and `s ∈ [0, T]`, where
`X̂, X̄` are the interpolants of the scheme run with `h^δ`. -/
theorem increment_moment_bound {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α γ μ q : ℝ) (hA4 : Assumption4 f g α γ μ q)
    (h : SDEState m → ℝ) (α' β' : ℝ) (hA2 : Assumption2 f h α' β')
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T)
    (hδ : ℝ → SDEState m → ℝ) (hA3 : Assumption3 (T : ℝ) h hδ)
    (hδ_meas : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Measurable (hδ δ)) :
    ∀ p : ℝ, 4 ≤ p → ∃ C3 : ℝ, 0 < C3 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ s ∈ Set.Icc (0 : ℝ≥0) T,
        ∫⁻ ω, ‖Xhat f g (hδ δ) x0 W s ω - Xbar f g (hδ δ) x0 W s ω‖ₑ ^ (2 * p) ∂P
          ≤ ENNReal.ofReal (C3 * δ ^ p) := by sorry

end AdaptiveEM.Finite
