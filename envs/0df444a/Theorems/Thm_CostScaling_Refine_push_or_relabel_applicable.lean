-- Prove2me | Theorems.Thm_CostScaling_Refine_push_or_relabel_applicable
-- name    : CostScaling.Refine.push_or_relabel_applicable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:26:23.967194+00:00
-- url     : https://prove2.me/theorems/39ff9415-e520-4edb-a6e9-5158c78b10b6
-- title:
--   Lemma 5.1 — an active vertex admits an update
-- statement:
--   Let a circulation network be feasible, so some circulation exists. Let $f$ be a pseudoflow that is $\varepsilon$-optimal with respect to prices $p$, and let $v$ have positive excess. Then either a push applies to an arc $(v,w)$ for some $w$, or a relabel applies at $v$:
--
--   $$
--   e_f(v)>0\quad\Longrightarrow\quad \bigl(\exists w,\ \operatorname{PushApplicable}(v,w)\bigr)\ \lor\ \operatorname{RelabelApplicable}(v).
--   $$
--
--   This is the progress fact used to connect the loop guard with flow conservation. Feasibility also ensures that the relabel action has an outgoing residual arc and an attained minimum, so an applicable operation is a genuine next step.
--
--   **Formalization Note** The formal conclusion explicitly produces a successor state for a relabel; Figure 5 says an empty relabel minimum signals infeasibility.
-- source:
--   Goldberg & Tarjan, MIT/LCS/TM-333 (July 1987), Lemma 5.1, p. 19; https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-333.pdf

import Mathlib
import Definitions.Def_CostScaling_Refine_Run

namespace CostScaling.Refine

/-- Lemma 5.1, p. 19. Feasibility also rules out an empty relabel minimum. -/
theorem push_or_relabel_applicable {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ε : ℝ) (s : State V)
    (hfeasible : ∃ g, CycleCanceling.MinMean.IsCirculation N g)
    (hopt : IsEpsOptimal N ε s.f s.p) (v : V) (hv : IsActive N s.f v) :
    (∃ w, PushApplicable N s v w) ∨ (∃ t, IsRelabelStep N ε s v t) := by sorry

end CostScaling.Refine
