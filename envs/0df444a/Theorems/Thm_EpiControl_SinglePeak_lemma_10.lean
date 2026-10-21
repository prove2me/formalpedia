-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_10
-- name    : EpiControl.SinglePeak.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:25.57364+00:00
-- url     : https://prove2.me/theorems/7667f7c6-f772-45e6-9b4f-6ce82c80cb07
-- title:
--   Lemma 10, p. 16 (PDF 17) — where η∗ ≤ 0 the optimal control is maximal and continuous
-- statement:
--   Let $\beta^*$ be an optimal control with SIR path $(s^*,i^*)$ and multipliers $\lambda_1^*,\lambda_2^*$ as in Lemma 9, and suppose the optimality condition (12) holds for **every** $t\in[0,T]$. Put $\eta^*=\lambda_2^*-\lambda_1^*$. If $t_0\in[0,T]$ satisfies $\eta^*(t_0)\le 0$, then
--   $$\lim_{t\to t_0}\beta^*(t)=\beta^*(t_0)=\bar b,$$
--   the limit being taken over $t\in[0,T]$.
--
--   This lemma is used to show that the costate $\eta^*$ is positive (Lemma 12).
--
--   **Formalization Note** The limit is `Tendsto β (𝓝[Icc 0 T] t₀) (𝓝 b̄)`, i.e. within $[0,T]$; the condition "(12) for all $t$" is the explicit hypothesis `h12`.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 16 (PDF 17), Lemma 10

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_10 (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (lam1 lam2 : ℝ → ℝ)
    (hlam : P.IsMultiplier β s i lam1 lam2)
    (h12 : ∀ t ∈ Icc 0 P.T, P.ArgminAt ((lam2 t - lam1 t) * i t * s t) (β t))
    (t0 : ℝ) (ht0 : t0 ∈ Icc 0 P.T) (hη : lam2 t0 - lam1 t0 ≤ 0) :
    β t0 = P.bbar ∧ Tendsto β (𝓝[Icc 0 P.T] t0) (𝓝 P.bbar) := by sorry
end EpiControl.SinglePeak
