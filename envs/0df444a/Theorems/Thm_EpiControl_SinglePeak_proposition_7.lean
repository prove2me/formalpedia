-- Prove2me | Theorems.Thm_EpiControl_SinglePeak_proposition_7
-- name    : EpiControl.SinglePeak.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:38.714906+00:00
-- url     : https://prove2.me/theorems/34b52a2e-4506-42b2-a8bb-96ff08c5a27b
-- title:
--   Proposition 7, p. 11 (PDF 12) — under Assumption 1 every optimal policy is single-peaked and i∗ is strictly log-concave while measures escalate
-- statement:
--   Consider the controlled SIR model under the standing assumptions of §2, and suppose **Assumption 1** (limited capacity effects) holds:
--   $$\frac{v''(i)}{\gamma}<\frac{27}{4}\,\frac{\underline b}{\bar b-\underline b}\,\big|c'(\bar b-)\big|\qquad\text{for all } i\in[0,1].$$
--   Let $\beta^*$ be an optimal control with SIR path $(s^*,i^*)$. Then there is $t^*\in[0,T]$ such that:
--
--   1. $\beta^*$ is non-increasing on $[0,t^*]$ and non-decreasing on $[t^*,T]$, i.e. $\beta^*$ is quasi-convex (after a modification on a null set, see below);
--   2. the infected share $i^*$ is strictly log-concave on $[0,t^*]$, and thus has at most one local maximum on $[0,t^*]$.
--
--   Social-distancing measures are first escalated and then relaxed — never relaxed and then re-escalated — and during the escalation phase the epidemic curve has a single peak.
--
--   **Formalization Note** An optimal control is determined only up to a null set, so "$\beta^*$ is non-increasing on $[0,t^*]$" for an arbitrary version is false; the paper fixes the version by its convention (p. 7) that the argmin condition (6) holds at every $t$, which Lemma 13 justifies. The statement therefore provides, for every optimal $\beta^*$, an admissible $\hat\beta$ with $\hat\beta=\beta^*$ almost everywhere on $[0,T]$ (hence optimal with the same path) that is non-increasing on $[0,t^*]$ and non-decreasing on $[t^*,T]$. Part 2 concerns $i^*$, which does not depend on the version. Strict log-concavity is strict concavity of $t\mapsto\log i^*(t)$ on $[0,t^*]$; since $i^*>0$ on $[0,T]$, the Lean `Real.log` is the true logarithm there. "At most one local maximum" means two points of $[0,t^*]$ that are local maxima of $i^*$ relative to $[0,t^*]$ coincide. $c'(\bar b-)$ is the parameter `dc` with its defining limit inside Assumption 1.
-- source:
--   Kruse & Strack, Optimal Control of an Epidemic through Social Distancing, Cowles Foundation Discussion Paper No. 2229R (rev. July 2020), p. 11 (PDF 12), Proposition 7; Assumption 1, p. 10 (PDF 11)

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiControl.SinglePeak

theorem proposition_7 (P : Params) (hP : P.Standing) (dc : ℝ) (hA1 : P.Assumption1 dc)
    (β s i : ℝ → ℝ) (hopt : P.IsOptimal β s i) :
    ∃ tstar ∈ Icc 0 P.T, ∃ βh : ℝ → ℝ,
      P.Admissible βh ∧ βh =ᵐ[volume.restrict (Icc 0 P.T)] β ∧
      AntitoneOn βh (Icc 0 tstar) ∧ MonotoneOn βh (Icc tstar P.T) ∧
      StrictConcaveOn ℝ (Icc 0 tstar) (fun t => Real.log (i t)) ∧
      ∀ t₁ ∈ Icc 0 tstar, ∀ t₂ ∈ Icc 0 tstar,
        IsLocalMaxOn i (Icc 0 tstar) t₁ → IsLocalMaxOn i (Icc 0 tstar) t₂ → t₁ = t₂ := by sorry
end EpiControl.SinglePeak
