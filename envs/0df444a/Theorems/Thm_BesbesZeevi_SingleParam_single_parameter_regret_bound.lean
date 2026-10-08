-- Prove2me | Theorems.Thm_BesbesZeevi_SingleParam_single_parameter_regret_bound
-- name    : BesbesZeevi.SingleParam.single_parameter_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:38:15.413269+00:00
-- url     : https://prove2.me/theorems/635d1a37-4a0d-49fc-91d3-7e6db24fa336
-- title:
--   Proposition 5: Algorithm 3 has regret $O\big((\log\log n)(\log n)^{1/2}/n^{1/2}\big)$
-- statement:
--   Fix a market with prices $0<\underline p<\overline p<p_\infty$, inventory $x>0$ and horizon $T>0$, a one-parameter demand family $\lambda(\cdot;\theta)$, $\theta\in\Theta$, satisfying Assumptions 1, 2 and 3, and a measurable selection $(p^u,p^c)$. Let $\pi_n=\pi(\ell_n,\Delta^{(1)}_n,\dots,\Delta^{(\ell_n)}_n)$ be Algorithm 3 with the tuning (19)–(20). Then there are $C>0$ and $n_0$ such that for every unit-rate Poisson process on a probability space, every $n\ge n_0$ and every $\theta\in\Theta$,
--
--   $$
--   \mathcal R^\pi_n(x,T;\theta)\le C\,\frac{(\log\log n)(\log n)^{1/2}}{n^{1/2}} .
--   $$
--
--   Equivalently, $\sup_{\theta\in\Theta}\mathcal R^\pi_n(x,T;\theta)=O\big((\log\log n)(\log n)^{1/2}/n^{1/2}\big)$. Up to logarithmic factors this matches the $n^{-1/2}$ lower bound of Proposition 4, so with a single unknown parameter continued learning near the optimal price is rate-optimal.
--
--   **Formalization Note** The $O(\cdot)$ is rendered as "there exist $C$ and $n_0$", with $C$ and $n_0$ independent of $\theta$, of $n$ and of the Poisson process. The clause "asymptotically optimal" of the proposition is not formalized. The statement covers both cases $\lambda(\overline p;\theta)\le x/T$ and $\lambda(\overline p;\theta)>x/T$; the paper's proof treats only the first in detail. Probability spaces are taken in `Type`.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 18 (PDF p. 20), Proposition 5, eq. (21)

import Mathlib
import Definitions.Def_BesbesZeevi_SingleParam_PoissonProcess
import Definitions.Def_BesbesZeevi_SingleParam_Model
import Definitions.Def_BesbesZeevi_SingleParam_Family
import Definitions.Def_BesbesZeevi_SingleParam_Tuning
import Definitions.Def_BesbesZeevi_SingleParam_Algorithm

open MeasureTheory

namespace BesbesZeevi.SingleParam

/-- Proposition 5 (Besbes–Zeevi 2009, p. 18), bound (21): under Assumptions 1–3, the policies
`π_n = π(ℓ_n, Δ^{(1)}_n, …, Δ^{(ℓ_n)}_n)` of Algorithm 3 with the tuning (19)–(20) satisfy
`sup_{θ ∈ Θ} R^π_n(x, T; θ) = O((log log n)(log n)^{1/2} / n^{1/2})`: there are `C > 0` and
`n₀` with `R^π_n(x, T; θ) ≤ C (log log n)(log n)^{1/2} / n^{1/2}` for all `n ≥ n₀` and all
`θ ∈ Θ`, for every unit-rate Poisson process. -/
theorem single_parameter_regret_bound (D : Market) (F : Family D) (σ : Selection D F) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (N : PoissonProcess Ω P), ∀ n : ℕ, n₀ ≤ n → ∀ θ ∈ F.Θ,
          tunedRegret N D F σ n θ
            ≤ C * Real.log (Real.log n) * Real.sqrt (Real.log n) / Real.sqrt n := by sorry

end BesbesZeevi.SingleParam
