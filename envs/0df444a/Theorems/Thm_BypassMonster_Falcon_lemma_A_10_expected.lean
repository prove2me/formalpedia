-- Prove2me | Theorems.Thm_BypassMonster_Falcon_lemma_A_10_expected
-- name    : BypassMonster.Falcon.lemma_A_10_expected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:52.091483+00:00
-- url     : https://prove2.me/theorems/84d81dec-a6d0-42b8-91fc-cb33f9cb6b9a
-- title:
--   Lemma A.10 (expected part), p. 1927 — E[regret] ≤ Σ_{t=τ₁+1}^T 7.15K/γ_{m(t)} + √K τ₁ + Tδ/2
-- statement:
--   Consider Setup 2 with horizon $M=m(T)$, for a number of rounds $T\ge1$. The regret of FALCON+ after $T$ rounds is integrable and its expectation satisfies
--   $$\mathbb E\Big[\sum_{t=1}^T\big(r_t(\pi_{f^*}(x_t))-r_t(a_t)\big)\Big]\le\sum_{t=\tau_1+1}^{T}\frac{7.15\,K}{\gamma_{m(t)}}+\sqrt K\,\tau_1+\frac{T\delta}{2}.$$
--
--   This is the in-expectation form of the regret guarantee.
--
--   **Formalization Note** The paper states this sentence without bounded rewards, using Condition (5); here rewards are in $[0,1]$ (the standing model of §1.2), so this is the bounded-reward case of the printed claim. Finite $\mathcal X$. The sum over $t$ is empty when $T\le\tau_1$.
-- source:
--   Simchi-Levi & Xu, Math. Oper. Res. 47(3) (2022), Lemma A.10 (first sentence) and its proof, p. 1927

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model

namespace BypassMonster.Falcon

open MeasureTheory ProbabilityTheory

/-- **Lemma A.10**, first sentence (p. 1927), with `[0,1]` rewards: the expected regret of FALCON+
after `T` rounds is at most `∑_{t=τ_1+1}^{T} 7.15 K/γ_{m(t)} + √K τ_1 + Tδ/2` (and the regret is
integrable). -/
theorem lemma_A_10_expected
    {X : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (ν : Kernel X (Fin K → ℝ)) [IsMarkovKernel ν]
    (A : Params X K) (πstar : X → Fin K)
    (T : ℕ) (hT : 1 ≤ T) (hS : Setup2 DX ν A πstar (epochOf A.τ T)) :
    Integrable (A.regret πstar T) (canonMeasure DX ν) ∧
    ∫ ω, A.regret πstar T ω ∂(canonMeasure DX ν)
      ≤ ∑ t ∈ Finset.Ioc (A.τ 1) T, 715 / 100 * (K : ℝ) / A.gamma (epochOf A.τ t)
        + Real.sqrt (K : ℝ) * (A.τ 1 : ℝ) + (T : ℝ) * A.δ / 2 := by sorry

end BypassMonster.Falcon
