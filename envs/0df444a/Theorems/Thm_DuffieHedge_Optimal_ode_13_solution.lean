-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_ode_13_solution
-- name    : DuffieHedge.Optimal.ode_13_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:42.350978+00:00
-- url     : https://prove2.me/theorems/de0272cb-0f20-4478-be98-cc3179979b04
-- title:
--   §3.3, p. 6 — the solution of (13) is $H_t=H_0\exp(-\int_0^t m_s^2/v_s^2\,ds)$
-- statement:
--   Let $T\ge0$, let $m,v$ be measurable functions, bounded on $[0,T]$, with $|v_t|\ge\delta>0$ on $[0,T]$. Let $H$ be a real function on $[0,T]$ such that $s\mapsto(m_s^2/v_s^2)H_s$ is integrable on $[0,T]$ and
--
--   $$H_t=H_0-\int_0^t\frac{m_s^2}{v_s^2}H_s\,ds\qquad(t\in[0,T]),$$
--
--   the integral form of (13). Then
--
--   $$H_t=H_0\exp\Big(-\int_0^t\frac{m_s^2}{v_s^2}\,ds\Big)\qquad\text{for every }t\in[0,T].$$
--
--   This is the uniqueness of solutions of the linear ODE (13); together with $H_0=0$ it forces $H\equiv0$.
--
--   **Formalization Note.** Stated for an arbitrary real function satisfying (13) in integral form, independently of the stochastic model.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, after Lemma 2, p. 6

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- §3.3, after Lemma 2 (p. 6): the solution of (13). If `m, v` are measurable and bounded on
`[0, T]`, `v` is bounded away from zero, and a real function `H` satisfies (13) in integral form,
`H_t = H_0 − ∫₀ᵗ (m_s²/v_s²) H_s ds` on `[0, T]`, then
`H_t = H_0 exp(−∫₀ᵗ m_s²/v_s² ds)` on `[0, T]`. -/
theorem ode_13_solution (T : ℝ≥0) (m v : ℝ≥0 → ℝ) (hm : Measurable m) (hv : Measurable v)
    (hbd : ∃ K : ℝ, ∀ t ≤ T, |m t| ≤ K ∧ |v t| ≤ K)
    (hv0 : ∃ δ : ℝ, 0 < δ ∧ ∀ t ≤ T, δ ≤ |v t|)
    (H : ℝ≥0 → ℝ)
    (hint : IntegrableOn (fun s : ℝ => m s.toNNReal ^ 2 / v s.toNNReal ^ 2 * H s.toNNReal)
      (Set.Icc (0 : ℝ) T))
    (hode : ∀ t ≤ T, H t = H 0 - ∫ s in Set.Icc (0 : ℝ) t,
      m s.toNNReal ^ 2 / v s.toNNReal ^ 2 * H s.toNNReal) :
    ∀ t ≤ T, H t = H 0 * Real.exp (-∫ s in Set.Icc (0 : ℝ) t,
      m s.toNNReal ^ 2 / v s.toNNReal ^ 2) := by sorry

end DuffieHedge.Optimal
