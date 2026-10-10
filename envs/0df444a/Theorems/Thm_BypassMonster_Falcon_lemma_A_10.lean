-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_10
-- name    : BypassMonster.Falcon.lemma_A_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:58.644262+00:00
-- url     : https://prove2.me/theorems/08263999-2e7b-4dff-920b-d479804cc551
-- title:
--   Lemma A.10 (high-probability part), p. 1927 — w.p. ≥ 1−δ, regret ≤ Σ_{t=τ₁+1}^T 7.15K/γ_{m(t)} + τ₁ + √(8T log(2/δ))
-- statement:
--   Consider Setup 2 with horizon $M=m(T)$, for a number of rounds $T\ge1$, with rewards in $[0,1]$. With probability at least $1-\delta$, the regret of FALCON+ after $T$ rounds satisfies
--   $$\sum_{t=1}^T\big(r_t(\pi_{f^*}(x_t))-r_t(a_t)\big)\le\sum_{t=\tau_1+1}^{T}\frac{7.15\,K}{\gamma_{m(t)}}+\tau_1+\sqrt{8T\log(2/\delta)}.$$
--
--   This is the round-by-round form of the paper's main regret guarantee, from which Theorem 2 follows by grouping rounds into epochs.
--
--   **Formalization Note** Stated in failure form: the set where the regret exceeds the bound has outer measure at most $\delta$. The learning rates $\gamma_m$ are those of Algorithm 2 with the same $\delta$. Finite $\mathcal X$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.10 (second sentence) and its proof, p. 1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.10**, second sentence (p. 1927): with `[0,1]` rewards, with probability at least
`1 − δ` the regret of FALCON+ after `T` rounds is at most
`∑_{t=τ_1+1}^{T} 7.15 K/γ_{m(t)} + τ_1 + √(8T log(2/δ))`. Stated in failure form. -/
theorem lemma_A_10
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (T : ℕ) (hT : 1 ≤ T) (hS : Setup2 DX ν A πstar (epochOf A.τ T)) :
    canonMeasure DX ν {ω | ∑ t ∈ Finset.Ioc (A.τ 1) T, 715 / 100 * (K : ℝ) / A.gamma (epochOf A.τ t)
          + (A.τ 1 : ℝ) + Real.sqrt (8 * (T : ℝ) * Real.log (2 / A.δ)) < A.regret πstar T ω}
      ≤ ENNReal.ofReal A.δ := by sorry

end BypassMonster.Falcon
