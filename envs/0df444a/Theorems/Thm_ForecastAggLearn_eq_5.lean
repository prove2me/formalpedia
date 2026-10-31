-- Prove2me | Theorems.Thm_ForecastAggLearn_eq_5
-- name    : ForecastAggLearn.eq_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:47.809293+00:00
-- url     : https://prove2.me/theorems/6ec01fce-bfd0-4b6b-b407-3ecb66abd373
-- title:
--   Eq. (5) — $\mathbb E_{\omega_t}[\overline L_t(h)]=\tilde L(h\cdot\tilde z_t+\tilde\mu_t)$
-- statement:
--   Let $\tilde z\in\mathbb R^n$, $\tilde\mu\in\mathbb R$, $h\in\mathbb R^n$, and let $\omega$ be a Bernoulli variable with success probability $q\in[0,1]$ (in the paper $q=r^*=\mathbb E[\omega_t\mid\tilde z_t]$). With $\overline L$ the loss of eq. (4),
--
--   $$
--   \mathbb E_{\omega}\bigl[\overline L(h)\bigr]=q\,\overline L(h)\big|_{\omega=1}+(1-q)\,\overline L(h)\big|_{\omega=0}=-(q-1)(h\cdot\tilde z+\tilde\mu)+\ln\bigl(1+\exp(-h\cdot\tilde z-\tilde\mu)\bigr)=\tilde L(h\cdot\tilde z+\tilde\mu).
--   $$
--
--   So the per-period loss (4), which depends only on the realized state, is an unbiased version of the expected loss $\tilde L$; regret bounds for the realized losses transfer to expected regret.
--
--   Differences from the source:
--   - encoding: E_{ω_t}[L̄_t(h)] with E[ω_t | z̃_t] = r*(z̃_t) → q · L̄(h)|_{ω=1} + (1 − q) · L̄(h)|_{ω=0} for every q ∈ [0, 1]; reason: the expectation of a function of a Bernoulli(q) state; r* ranges over [0, 1]
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, eqs. (4)–(5), p.18

import Mathlib
import Definitions.Def_ForecastAggLearn_barL

namespace ForecastAggLearn

/-- **Eq. (5): the expected per-period loss.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, eqs. (4)–(5), p.18: with
`L̄_t(h) = (1 − ω_t)(h · z̃_t + µ̃_t) + ln(1 + exp(−h · z̃_t − µ̃_t))` (4), and `ω_t` a Bernoulli
variable with success probability `r*`, "∀h ∈ ℝⁿ, t ∈ [T] : E_{ω_t}[L̄_t(h)] = L̃(h · z̃_t + µ̃_t)"
where `L̃(r̃) = −(r* − 1) r̃ + ln(1 + exp(−r̃))` (p.16).

**Formalization Note.** `q` is the success probability `r* = E[ω_t | z̃_t]`, and the expectation
over `ω_t` is `q L̄_t(h)|_{ω=1} + (1 − q) L̄_t(h)|_{ω=0}`. -/
theorem eq_5 {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (μt : ℝ) (h : EuclideanSpace ℝ (Fin n))
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * barL z μt true h + (1 - q) * barL z μt false h =
      -(q - 1) * (inner ℝ h z + μt) + Real.log (1 + Real.exp (-(inner ℝ h z + μt))) := by sorry

end ForecastAggLearn
