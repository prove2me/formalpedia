-- Prove2me | Theorems.Thm_DuffieHedge_Optimal_dZ_ito
-- name    : DuffieHedge.Optimal.dZ_ito
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:17:15.545688+00:00
-- url     : https://prove2.me/theorems/7f33f67f-da02-42fb-a48b-02786a4075f9
-- title:
--   Proof of Lemma 2, p. 5 — $dZ_t=(\gamma_t+\mu_t)Z_t\,dt+\sigma_tZ_t\,dB_t$
-- statement:
--   Under the standing hypotheses, the tracking process $Z_t=k\exp(-\int_t^T\gamma_s\,ds)\,S_t$ of (9), with $\gamma_t=m_t\sigma_t\rho_t/v_t-\mu_t$, is an Itô process on $[0,T]$:
--
--   $$dZ_t=(\gamma_t+\mu_t)Z_t\,dt+\sigma_tZ_t\,dB_t,\qquad Z_0=k\exp\Big(-\int_0^T\gamma_s\,ds\Big)S_0.$$
--
--   This is the first step in the computation of the inner-product function $H$ of (12).
--
--   **Formalization Note.** The paper's display omits the $dt$ after the drift; the drift term is $(\gamma_t+\mu_t)Z_t\,dt$, which is what Itô's lemma gives. The equation is in Peng's integral sense: for every $t\in[0,T]$, almost surely $Z_t=Z_0+\int_0^t(\gamma_s+\mu_s)Z_s\,ds+\int_0^t\sigma_sZ_s\,dB_s$, with $Z$ progressive and $\sup_{t\le T}E Z_t^2<\infty$.
-- source:
--   Duffie and Richardson, Mean-Variance Hedging in Continuous Time, Ann. Appl. Probab. 1(1) (1991), §3.3, proof of Lemma 2, p. 5

import Mathlib
import Definitions.Def_DuffieHedge_Optimal_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DuffieHedge.Optimal

/-- Proof of Lemma 2 (p. 5): the tracking process (9) is an Itô process,
`dZ_t = (γ_t + μ_t) Z_t dt + σ_t Z_t dB_t`, with `Z₀ = k exp(−∫₀ᵀ γ_s ds) S₀`
(the printed display omits the `dt`). -/
theorem dZ_ito {Ω : Type*} [MeasurableSpace Ω] (M : Market Ω) (hM : M.Standing) (k : ℝ) :
    Peng1990.SMP.IsItoProcess M.filt M.P M.T M.BE
      (fun _ : Unit => k * Real.exp (-∫ s in (0 : ℝ)..(M.T : ℝ), M.γ s.toNNReal) * M.S0)
      (fun s ω _ => (M.γ s + M.μ s) * M.Z k s ω)
      (fun j s ω _ => if j = 0 then M.σ s * M.Z k s ω else 0)
      (fun t ω _ => M.Z k t ω) := by sorry

end DuffieHedge.Optimal
