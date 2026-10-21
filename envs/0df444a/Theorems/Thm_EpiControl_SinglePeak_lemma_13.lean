-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_lemma_13
-- name    : EpiControl.SinglePeak.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:32.19483+00:00
-- url     : https://prove2.me/theorems/cc143788-a3b7-4a7f-8845-c6a6b72701b2
-- title:
--   Lemma 13, p. 20 (PDF 21) — an optimal policy may be chosen with β∗(t) ∈ argmin[g∗(t)b + c(b)] for all t
-- statement:
--   Let $\beta^*$ be an optimal policy with SIR path $(s^*,i^*)$, let $\eta^*$ be a costate as in Proposition 1 and $g^*(t)=\eta^*(t)i^*(t)s^*(t)$ the gain. Then there is an optimal policy $\hat\beta$ with the same SIR path $(s^*,i^*)$, equal to $\beta^*$ almost everywhere on $[0,T]$, such that
--   $$\hat\beta(t)\in\arg\min_{b\in B}\big[g^*(t)b+c(b)\big]\qquad\text{for all } t\in[0,T].$$
--
--   This justifies the paper's convention (p. 7) that the optimality condition (6) holds at every time, not only almost everywhere.
--
--   **Formalization Note** The page states "there exists an optimal policy such that …"; its proof starts from an arbitrary optimal $\beta^*$ and modifies it on a null set. This is the per-$\beta^*$ form the proof establishes, which implies the printed existential.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 20 (PDF 21), Lemma 13 and its proof (pp. 20–21)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem lemma_13 (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    ∃ βh : ℝ → ℝ, P.IsOptimal βh s i ∧
      βh =ᵐ[volume.restrict (Icc 0 P.T)] β ∧
      ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (βh t) := by sorry
end EpiControl.SinglePeak
