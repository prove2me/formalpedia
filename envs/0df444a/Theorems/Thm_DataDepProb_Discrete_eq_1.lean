-- Prove2me | Theorems.Thm_DataDepProb_Discrete_eq_1
-- name    : DataDepProb.Discrete.eq_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:46.808826+00:00
-- url     : https://prove2.me/theorems/ab6d913c-bf8b-4a9b-adf1-99f0567fc270
-- title:
--   §5, Eq. (1) — the answer $2E_q[f]-E_u[f]$ lies in $[0,1]$ and its squared error is $4(E_q[f]-E_{\tilde D}[f])^2$
-- statement:
--   Let $D\in\Delta_d$, $u$ the uniform distribution and $\tilde D=(D+u)/2$. For every $q\in\tilde\Delta_d$ and $f\in[0,1]^{[d]}$,
--   $$2E_q[f]-E_u[f]\in[0,1],\qquad \big(2E_q[f]-E_u[f]-E_D[f]\big)^2=4\big(E_q[f]-E_{\tilde D}[f]\big)^2 .$$
--   The identity converts an estimate of $E_{\tilde D}[f]$ into one of $E_D[f]$; it is how the estimator's risk is expressed through $\ell_t$.
--
--   Differences from the source:
--   - encoding: $[d]$, $f\in[0,1]^{[d]}$ → `Fin d`, `f : Fin d → ℝ` with `0 ≤ f x ≤ 1`; reason: same objects.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 12, §5, Eq. (1)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex

namespace DataDepProb.Discrete

/-- §5, Eq. (1) (p. 12). For `D ∈ ∆_d`, every `q ∈ ∆̃_d` and every `f ∈ [0, 1]^[d]`:
`2E_q[f] − E_u[f] ∈ [0, 1]` and `(2E_q[f] − E_u[f] − E_D[f])² = 4(E_q[f] − E_{D̃}[f])²`,
where `u` is uniform on `[d]` and `D̃ = (D + u)/2`. -/
theorem eq_1 {d : ℕ} (D : Fin d → ℝ) (hD : D ∈ simplex d) (q f : Fin d → ℝ)
    (hq : q ∈ truncSimplex d) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    answer q f ∈ Set.Icc (0 : ℝ) 1 ∧
      (answer q f - expect D f) ^ 2 = 4 * (expect q f - expect (shift D) f) ^ 2 := by sorry

end DataDepProb.Discrete
