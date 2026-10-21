-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_proposition_2_iii
-- name    : EpiControl.SinglePeak.proposition_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:44.334306+00:00
-- url     : https://prove2.me/theorems/981c3587-b8fb-4903-aee4-2eee4c879cd3
-- title:
--   Proposition 2 (iii), p. 7 (PDF 8) — any optimal control is non-increasing in the gain g∗
-- statement:
--   Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$ and costate $\eta^*$ as in Proposition 1, let $g^*=\eta^*i^*s^*$, and suppose (following the paper's convention, p. 7) that $\beta^*(t)\in\arg\min_{b\in B}[g^*(t)b+c(b)]$ for every $t\in[0,T]$. Then for all $t,t'\in[0,T]$
--   $$g^*(t)>g^*(t')\ \Longrightarrow\ \beta^*(t)\le\beta^*(t').$$
--
--   The more valuable a reduction of transmission, the stricter the measures.
--
--   **Formalization Note** The convention that (6) holds for all $t$ is the explicit hypothesis `hconv`; Lemma 13 shows every optimal policy can be modified on a null set to satisfy it.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 7 (PDF 8), Proposition 2 (iii); convention p. 7

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem proposition_2_iii (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η)
    (hconv : ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (β t)) :
    ∀ t ∈ Icc 0 P.T, ∀ t' ∈ Icc 0 P.T,
      gain η s i t' < gain η s i t → β t ≤ β t' := by sorry
end EpiControl.SinglePeak
