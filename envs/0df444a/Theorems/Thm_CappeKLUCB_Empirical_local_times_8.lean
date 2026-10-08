-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_local_times_8
-- name    : CappeKLUCB.Empirical.local_times_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:25.983963+00:00
-- url     : https://prove2.me/theorems/024e5ab7-6a44-4bdf-9128-22a7c894e640
-- title:
--   (8), p. 10 — Σ_t ℙ{ν̂_{a,N_a(t)} ∈ 𝒞_{μ†,f(t)/N_a(t)}, A_{t+1} = a} ≤ Σ_{n=1}^{T−K} ℙ{ν̂_{a,n} ∈ 𝒞_{μ†,f(T)/n}} for Algorithm 3
-- statement:
--   In the setting of the previous display (a $K$-armed bandit with $K\ge2$ and reward distributions in $\mathcal F$, a run of Algorithm 3 with $f(t)=\log t+\log\log t$), for every arm $a$, every $\mu^\dagger\in\mathbb R$ and every $T$,
--   $$\sum_{t=K}^{T-1}\mathbb P\bigl\{\hat\nu_{a,N_a(t)}\in\mathcal C_{\mu^\dagger,f(t)/N_a(t)} \text{ and } A_{t+1}=a\bigr\} \le \sum_{n=1}^{T-K}\mathbb P\bigl\{\hat\nu_{a,n}\in\mathcal C_{\mu^\dagger,f(T)/n}\bigr\},$$
--   where $\hat\nu_{a,n}$ is the empirical distribution of the first $n$ rewards of arm $a$.
--
--   The right-hand side no longer involves the algorithm: it concerns the empirical distributions of an i.i.d. sample of fixed size $n$ from $\nu_a$, which is what makes the remaining sum amenable to large-deviation bounds for empirical distributions.
--
--   **Formalization Note** Same representation as for the display after (7): reward stacks, pathwise $[0,1]$ rewards, measurable arm choices, probabilities applied as outer measures. When $T\le K$ both sides are empty sums.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, pp. 9–10, (8), for Algorithm 3 of p. 15 with f of Theorem 2

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- Display (8), Cappé et al., arXiv:1210.1136v4, p. 10, for Algorithm 3 (p. 15) with
`f(t) = log t + log log t`:
`∑_{t=K}^{T-1} ℙ{ν̂_{a,N_a(t)} ∈ 𝒞_{μ†, f(t)/N_a(t)}, A_{t+1} = a} ≤ ∑_{n=1}^{T-K} ℙ{ν̂_{a,n} ∈ 𝒞_{μ†, f(T)/n}}`. -/
theorem local_times_8 {K : ℕ} (hK : 2 ≤ K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Fin K → ℕ → Ω → ℝ) (μ : Fin K → ℝ) (hX : IsStochasticBandit P X μ)
    (hF : ∀ a, IsFinSupp01 (P.map (X a 0))) (hbdd : ∀ a k ω, X a k ω ∈ Set.Icc (0 : ℝ) 1)
    (I : ℕ → Ω → Fin K) (hI : ∀ t, Measurable (I t)) (hrun : IsEmpKLUCBRun f₂ X I)
    (a : Fin K) (μdag : ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Ico K T,
        P.real {ω | InC μdag (f₂ t / (pullCount I a t ω : ℝ))
            (empMeasure (fun k => X a k ω) (pullCount I a t ω)) ∧ I (t + 1) ω = a}
      ≤ ∑ n ∈ Finset.Icc 1 (T - K),
          P.real {ω | InC μdag (f₂ T / (n : ℝ)) (empMeasure (fun k => X a k ω) n)} := by sorry

end CappeKLUCB.Empirical
