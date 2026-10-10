-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_7
-- name    : BypassMonster.Falcon.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:27:49.564918+00:00
-- url     : https://prove2.me/theorems/5ac4def0-d69c-4449-9c93-061676d4253a
-- title:
--   Lemma A.7, p. 1924 (Setup 2) — on Γ₂, for t > τ₁: |ℛ̂ₜ(π) − ℛ(π)| ≤ √𝒱ₜ(π) √K/(2γ_{m(t)})
-- statement:
--   Consider Setup 2 and an outcome in the event $\Gamma_2$. For every epoch $m\ge2$ (the rounds $t>\tau_1$) and every policy $\pi\in\Psi$,
--   $$\big|\hat{\mathcal R}_m(\pi)-\mathcal R(\pi)\big|\le\frac{\sqrt{\mathcal V_m(\pi)}\,\sqrt K}{2\gamma_m},$$
--   where $\hat{\mathcal R}_m(\pi)=\mathbb E_x[\hat f_m(x,\pi(x))]$, $\mathcal R(\pi)=\mathbb E_x[f^*(x,\pi(x))]$ and $\mathcal V_m(\pi)=\max_{1\le n\le m-1}V(p_n,\pi)$.
--
--   The predicted reward of a policy is accurate exactly to the extent that earlier epochs explored the actions that policy takes.
--
--   **Formalization Note** The paper states the lemma for both Setup 1 (on $\Gamma_1$) and Setup 2 (on $\Gamma_2$); this is the Setup 2 branch. Quantities indexed by a round $t$ are indexed by its epoch $m=m(t)$. $\Gamma_2$ is the event of Lemma A.2, encoded with the error of $\hat f_m$ under $p_{m-1}$. Finite $\mathcal X$, $[0,1]$ rewards.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.7 and its proof, pp. 1924–1925

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.7** (p. 1924), Setup 2 branch: on `Γ_2`, for every epoch `m ≥ 2` (rounds `t > τ_1`)
and every policy `π ∈ Ψ`, `|ℛ̂(π) − ℛ(π)| ≤ √(𝒱(π)) √K / (2γ_m)`, with `ℛ̂`, `𝒱` those of epoch `m`. -/
theorem lemma_A_7
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (M : ℕ) (hS : Setup2 DX ν A πstar M) (ω : Params.Omega X K) (hω : ω ∈ A.Gamma2 DX ν)
    (m : ℕ) (hm : 2 ≤ m) (π : X → Fin K) :
    |A.Rhat DX m ω π - R DX ν π|
      ≤ Real.sqrt (A.calV DX m ω π) * Real.sqrt (K : ℝ) / (2 * A.gamma m) := by sorry

end BypassMonster.Falcon
