-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_support_combined
-- name    : DataDrivenRO.FwdBwd.support_combined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:02:19.600443+00:00
-- url     : https://prove2.me/theorems/2731e8cc-36fe-4c2a-a287-1963614a68fa
-- title:
--   Proof of Theorem 6, p. ec5 — δ*(v|𝒰^{FB}_ε) = Σ_{vᵢ>0} vᵢm_{fi} + Σ_{vᵢ≤0} vᵢm_{bi} + min_λ λ log(1/ε) + (1/2λ)(Σ vᵢ²σ̄²)
-- statement:
--   Let $m_b\le m_f$ and $\bar\sigma_f,\bar\sigma_b>0$ in $\mathbb R^d$, $\varepsilon\in(0,1)$ and $v\in\mathbb R^d$. Then
--   $$\delta^*(v\mid\mathcal U^{FB}_\varepsilon) = \sum_{i:v_i>0}v_im_{fi}+\sum_{i:v_i\le0}v_im_{bi} + \inf_{\lambda>0}\Big\{\lambda\log(1/\varepsilon)+\frac{1}{2\lambda}\Big(\sum_{i:v_i>0}v_i^2\bar\sigma_{fi}^2+\sum_{i:v_i\le0}v_i^2\bar\sigma_{bi}^2\Big)\Big\}.$$
--
--   This is the result of combining the Lagrangian dual with the three sub-subproblems in the proof of Theorem 6; what remains is a one-dimensional minimisation in $\lambda$.
--
--   **Formalization Note** The page writes $\min_{\lambda\ge0}$; the statement uses the infimum over $\lambda>0$ (`IsGLB`), which is the same value and avoids the $1/(2\cdot 0)$ term. The constant sum is moved inside the infimum, which does not change it. The split $v_i>0$ / $v_i\le0$ is the proof's; it agrees with (24)'s $v_i\ge0$ / $v_i<0$ because the terms vanish at $v_i=0$.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, EC.1.4, proof of Theorem 6, display after "Combining the three sub-subproblems yields", p. ec5

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

namespace DataDrivenRO.FwdBwd

theorem support_combined {d : ℕ} (mb mf sf sb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hsf : ∀ i, 0 < sf i) (hsb : ∀ i, 0 < sb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    IsGLB
      ((fun lam : ℝ => (∑ i, if 0 < v i then v i * mf i else v i * mb i) +
          (lam * Real.log (1 / ε) +
            1 / (2 * lam) * ∑ i, (if 0 < v i then v i ^ 2 * sf i ^ 2 else v i ^ 2 * sb i ^ 2))) ''
        Set.Ioi 0)
      (RobustMDP.Shared.supportFunction (UFB mb mf sf sb ε) v) := by sorry

end DataDrivenRO.FwdBwd
