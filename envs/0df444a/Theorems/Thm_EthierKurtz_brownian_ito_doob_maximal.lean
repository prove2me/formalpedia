-- Prove2me | Theorems.Thm_EthierKurtz_brownian_ito_doob_maximal
-- name    : EthierKurtz.brownian_ito_doob_maximal
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T09:14:51.848984+00:00
-- url     : https://prove2.me/theorems/37f6491a-7724-4e60-9be4-599acfebfc41
-- title:
--   Doob maximal inequality for a continuous Brownian Itô integral with a bounded continuous adapted integrand
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion with its completed natural filtration $(\mathcal F_s)$, let $G$ be an $(\mathcal F_s)$-adapted process with continuous paths and $|G|\le C$, and let $J_t=\int_0^t G_s\,dW^j_s$ be a continuous version of its Itô integral against the coordinate $W^j$. Then for every $N\in\mathbb N$ and $\lambda>0$,
--
--   $$\lambda^2\,\mathbb P\Big(\sup_{t\le N}|J_t|>\lambda\Big)\le 2d\;\mathbb E\int_0^N G_u^2\,du.$$
--
--   Role: the maximal estimate for stochastic integrals that drives both the continuous-time strong law for $\ln X_i(t)/t$ and the short-time positivity estimate in the proof of Lemma 5.9 of Hening-Nguyen.
--
--   **Formalization Note**: the constant $2d$ is weaker than the sharp constant $1$ of Doob's $L^2$ inequality combined with the Itô isometry; any constant suffices for the applications.
-- source:
--   I. Karatzas, S. E. Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer 1991, https://doi.org/10.1007/978-1-4612-0949-2, Theorem 1.3.8(iv) (Doob's maximal inequality) and Proposition 3.2.10 (Itô isometry); X. Mao, Stochastic Differential Equations and Applications, 2nd ed., Horwood 2007, https://doi.org/10.1533/9780857099402, Theorem 1.3.8 and Theorem 1.5.21

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem brownian_ito_doob_maximal {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {G J : ℝ≥0 → Ω → ℝ}
    (hGm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (G s))
    (hGa : ∀ s, Measurable (G s)) (hGc : ∀ ω, Continuous fun s => G s ω) {C : ℝ}
    (hC : ∀ s ω, |G s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) G J)
    (hJc : ∀ ω, Continuous fun t => J t ω) (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ 2 * P.real {ω | ∃ t : ℝ≥0, t ≤ N ∧ lam < |J t ω|} ≤
      2 * d * ∫ ω, (∫ u in (0 : ℝ)..(N : ℝ), G u.toNNReal ω ^ 2) ∂P := by sorry

end EthierKurtz
