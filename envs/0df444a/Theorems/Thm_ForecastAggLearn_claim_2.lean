-- Prove2me | Theorems.Thm_ForecastAggLearn_claim_2
-- name    : ForecastAggLearn.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:27:37.61199+00:00
-- url     : https://prove2.me/theorems/2befbfa0-c242-4805-9938-a0fd6f1a0fa7
-- title:
--   Claim (2) — on non-extreme periods OGD has regret $\tilde O(n\sigma^{-1}\sqrt T)$
-- statement:
--   Let $A$ be a real $n\times m$ matrix with $\sigma_{\min}(A)\ge\sigma>0$ (i.e. $\sigma\|y\|\le\|Ay\|$), let $\tau,\beta\in(0,\tfrac12]$, and let $N\le T$ with $T\ge1$. For $t<N$ let $\tilde y_t\in\mathbb R^m$, a prior $\mu_t\in[\beta,1-\beta]$ with $\tilde\mu_t=\ln\frac{\mu_t}{1-\mu_t}$, and a state $\omega_t\in\{0,1\}$ be given, and suppose every period is **non-extreme**: the expert forecasts
--
--   $$
--   F_{i,t}=\bigl(1+\exp(-(A\tilde y_t)_i-\tilde\mu_t)\bigr)^{-1}\in[\tau,1-\tau]\qquad(i\in[n]).
--   $$
--
--   The aggregator runs online gradient descent (6) on $\tilde z_t=A\tilde y_t$ with
--
--   $$
--   W=\frac{\sqrt n}{\sigma},\qquad Z=\sqrt n\Bigl(\ln\frac{1-\tau}{\tau}+\ln\frac{1-\beta}{\beta}\Bigr),
--   $$
--
--   and forecasts $r_t=(1+\exp(-h_t\cdot\tilde z_t-\tilde\mu_t))^{-1}$. The optimal forecast is $r^*_t=(1+\exp(-\mathbf 1_m\cdot\tilde y_t-\tilde\mu_t))^{-1}$. Then, for every sequence of states,
--
--   $$
--   \sum_{t<N}l(r_t,\omega_t)\le\sum_{t<N}l(r^*_t,\omega_t)+2WZ\sqrt T .
--   $$
--
--   With $\tau=T^{-1/2}$ and a constant $\beta$, $2WZ\sqrt T=O(n\sigma^{-1}\sqrt T\log T)=\tilde O(n\sigma^{-1}\sqrt T)$, which is Claim (2) of the proof of Theorem 2.
--
--   **Formalization Note** The bound is pointwise (for every sequence of states), which implies the bound in expectation. $r^*_t$ and $F_{i,t}$ are written through the log-likelihood linearization (eq. (3)). Periods are 0-based and $h_0=0$.
--
--   Differences from the source:
--   - generalization: total regret in expectation → realized total log loss, for every sequence of states; reason: the pointwise bound implies the bound in expectation
--   - generalization: τ = T^{−1/2} and priors in [β, 1 − β] with β a constant (p.16) → any τ, β ∈ (0, 1/2] and any run length N ≤ T; reason: the paper's choice is the case τ = T^{−1/2}, β constant, N = number of non-extreme periods
--   - generalization: Õ(nσ^{−1}√T) → 2WZ√T with W = √n/σ and Z = √n(ln((1 − τ)/τ) + ln((1 − β)/β)); reason: for τ = T^{−1/2} and constant β this is O(nσ^{−1}√T log T)
--   - generalization: A the 0/1 evidence matrix → any real n × m matrix with σ‖y‖ ≤ ‖Ay‖; reason: the evidence matrix is the 0/1 case
--   - encoding: forecasts F_t and r*_t in probability space; σ_min(A) ≥ σ → F_{i,t} = logistic((Aỹ_t)_i + µ̃_t), r*_t = logistic(1_m·ỹ_t + µ̃_t); σ‖y‖ ≤ ‖Ay‖; reason: the linearization of eq. (3); the norm inequality is λ_min(AᵀA) ≥ σ²
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2, Claim (2), p.17; proof §4.2.1, pp.17–19

import Mathlib
import Definitions.Def_ForecastAggLearn_logLoss
import Definitions.Def_ForecastAggLearn_barL

namespace ForecastAggLearn

/-- **Claim (2): regret on non-extreme periods.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2, Claim (2), p.17: "Within T periods where all
realizations are non extreme, the total regret is at most Õ(nσ^{−1}√T)", proved in §4.2.1
(pp.17–19) by running OGD (6) on `z̃_t = Aỹ_t` with `W = σ^{−1}√n`.

Setting (pp.14–19): an `n × m` matrix `A` with `σ_min(A) ≥ σ > 0`; in each of `N ≤ T` periods a
vector `ỹ_t ∈ ℝ^m`, a prior `µ_t ∈ [β, 1 − β]` with `µ̃_t = ln(µ_t/(1 − µ_t))`, a state `ω_t`, and
non-extreme forecasts `F_{i,t} = (1 + exp(−(Aỹ_t)_i − µ̃_t))^{−1} ∈ [τ, 1 − τ]`. The aggregator runs
OGD (6) with `W = √n/σ` and `Z = √n (ln((1 − τ)/τ) + ln((1 − β)/β))` and forecasts
`(1 + exp(−h_t · z̃_t − µ̃_t))^{−1}`. Its realized total log loss exceeds that of the optimal
forecast `r*_t = (1 + exp(−1_m · ỹ_t − µ̃_t))^{−1}` by at most `2WZ√T = 2 n σ^{−1} √T (ln((1 − τ)/τ) + ln((1 − β)/β))`.

**Formalization Note.** Pointwise, for every sequence of states, not only in expectation; for
every thresholds `τ, β ∈ (0, 1/2]` (the paper: `τ = T^{−1/2}`, `β` constant), and every run length
`N ≤ T`, with the step `√(4W²/(Z²T))` of (6). Periods are 0-based; `h 0 = 0`. -/
theorem claim_2 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hA : ∀ y : EuclideanSpace ℝ (Fin m),
      σ * ‖y‖ ≤ ‖(WithLp.toLp 2 (A.mulVec y.ofLp) : EuclideanSpace ℝ (Fin n))‖)
    (τ β : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hβ0 : 0 < β) (hβ1 : β ≤ 1 / 2)
    (T N : ℕ) (hT : 0 < T) (hN : N ≤ T)
    (y : ℕ → Fin m → ℝ) (μ : ℕ → ℝ) (ω : ℕ → Bool)
    (hμ : ∀ t < N, μ t ∈ Set.Icc β (1 - β))
    (hF : ∀ t < N, ∀ i, (1 + Real.exp (-(A.mulVec (y t) i + Real.log (μ t / (1 - μ t)))))⁻¹ ∈
      Set.Icc τ (1 - τ))
    (h : ℕ → EuclideanSpace ℝ (Fin n)) (h0 : h 0 = 0)
    (hstep : ∀ t < N, h (t + 1) =
      let W := Real.sqrt n / σ
      let Z := Real.sqrt n * (Real.log ((1 - τ) / τ) + Real.log ((1 - β) / β))
      let v := h t - Real.sqrt (4 * W ^ 2 / (Z ^ 2 * T)) •
        gradient (barL (WithLp.toLp 2 (A.mulVec (y t))) (Real.log (μ t / (1 - μ t))) (ω t)) (h t)
      (W / max ‖v‖ W) • v) :
    ∑ t ∈ Finset.range N,
        logLoss (1 + Real.exp (-(inner ℝ (h t) (WithLp.toLp 2 (A.mulVec (y t)) :
          EuclideanSpace ℝ (Fin n)) + Real.log (μ t / (1 - μ t)))))⁻¹ (ω t) ≤
      ∑ t ∈ Finset.range N,
          logLoss (1 + Real.exp (-(∑ j, y t j + Real.log (μ t / (1 - μ t)))))⁻¹ (ω t) +
        ENNReal.ofReal (2 * (Real.sqrt n / σ) *
          (Real.sqrt n * (Real.log ((1 - τ) / τ) + Real.log ((1 - β) / β))) * Real.sqrt T) := by sorry

end ForecastAggLearn
