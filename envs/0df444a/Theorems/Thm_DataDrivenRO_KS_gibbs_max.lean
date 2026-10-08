-- Prove2me | Theorems.Thm_DataDrivenRO_KS_gibbs_max
-- name    : DataDrivenRO.KS.gibbs_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:21.646426+00:00
-- url     : https://prove2.me/theorems/9f763496-32e5-4b6f-b54b-62537ddcaaa8
-- title:
--   (EC.6), p. ec4 — max over q ∈ Δ of Σⱼ cⱼqⱼ − D(q, p) is log Σⱼ pⱼe^{cⱼ} (Gibbs variational principle)
-- statement:
--   Let $p\in\Delta_n$ be a probability vector and $c\in\mathbb R^n$. Then
--   $$\max_{q\in\Delta_n}\Big\{\sum_{j}c_jq_j-D(q,p)\Big\}=\log\sum_jp_je^{c_j},$$
--   where the maximum runs over the $q$ with $D(q,p)$ finite (that is, $q_j>0$ only where $p_j>0$), and it is attained, at $q_j=p_je^{c_j}/\sum_kp_ke^{c_k}$.
--
--   With $c_j=v_i\hat u^{(j)}_i/\lambda$ and $p=\theta_iq^L(\Gamma)+(1-\theta_i)q^R(\Gamma)$, and after multiplying by $\lambda$, this solves the inner maximization of the $i$-th subproblem in the proof of Theorem 5, with maximizer (EC.6).
--
--   **Formalization Note** "Maximum" is stated as `IsGreatest` of the set of attained values, which asserts both the upper bound and its attainment. $D$ is `relEntropy` with the finiteness predicate `AbsCont`; $p$ may have zero entries.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 5, (EC.6), p. ec4 (citing Boyd & Vandenberghe 2004, p. 93)

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem gibbs_max {n : ℕ} (c p : Fin n → ℝ) (hp : p ∈ stdSimplex ℝ (Fin n)) :
    IsGreatest
      {s | ∃ q ∈ stdSimplex ℝ (Fin n), AbsCont q p ∧
        s = ∑ j, c j * q j - relEntropy q p}
      (Real.log (∑ j, p j * Real.exp (c j))) := by sorry

end DataDrivenRO.KS
