-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_worst_case_eq_24
-- name    : DataDrivenRO.FwdBwd.worst_case_eq_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T14:01:26.22999+00:00
-- url     : https://prove2.me/theorems/645b4fa5-5207-4310-aad2-d533eb3e5d61
-- title:
--   Proof of Theorem 6, p. ec5 — (24) is the worst-case value of the bound (22) over the parameters of 𝒫^{FB}
-- statement:
--   Let $m_b\le m_f$ and $\bar\sigma_f,\bar\sigma_b>0$ in $\mathbb R^d$, $\varepsilon\in(0,1)$ and $v\in\mathbb R^d$. Consider the right-hand side of (22),
--   $$B(\mu,\sigma_f,\sigma_b) = \sum_i \mu_i v_i + \sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i<0}\sigma_{bi}^2v_i^2+\sum_{i:v_i\ge0}\sigma_{fi}^2v_i^2\Big)},$$
--   as a function of means $\mu_i\in[m_{bi},m_{fi}]$ and deviations $\sigma_{fi}\in[0,\bar\sigma_{fi}]$, $\sigma_{bi}\in[0,\bar\sigma_{bi}]$. Its greatest value over this box is attained and equals the right-hand side of (24):
--   $$\max B = \sum_{i:v_i\ge0}m_{fi}v_i+\sum_{i:v_i<0}m_{bi}v_i+\sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i\ge0}\bar\sigma_{fi}^2v_i^2+\sum_{i:v_i<0}\bar\sigma_{bi}^2v_i^2\Big)}.$$
--
--   This is the first step of the proof of Theorem 6, which passes from the bound (22) for a single distribution to a bound uniform over the confidence region.
--
--   **Formalization Note** The page's "worst-case value of (22) over $\mathcal P^{FB}$" ranges over distributions; the statement here ranges over the parameters (mean, deviation bounds) that the region constrains. The upper-bound half is what the proof of Theorem 6 uses; attainment over distributions would additionally need a distribution realising the extreme parameters, which is not claimed here.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 6, first sentence, p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem worst_case_eq_24 {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    IsGreatest
      ((fun p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin d → ℝ) => cssBound p.1 p.2.1 p.2.2 ε v) ''
        {p | ∀ i, (mb i ≤ p.1 i ∧ p.1 i ≤ mf i) ∧ (0 ≤ p.2.1 i ∧ p.2.1 i ≤ sf i) ∧
          (0 ≤ p.2.2 i ∧ p.2.2 i ≤ sb i)})
      (fbValue mb mf sf sb ε v) := by sorry

end DataDrivenRO.FwdBwd
