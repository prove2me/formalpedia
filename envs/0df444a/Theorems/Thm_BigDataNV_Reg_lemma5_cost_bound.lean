-- Prove2me | Theorems.Thm_BigDataNV_Reg_lemma5_cost_bound
-- name    : BigDataNV.Reg.lemma5_cost_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:53:09.635873+00:00
-- url     : https://prove2.me/theorems/4e2b188a-d7af-42e4-ac77-0f631953730e
-- title:
--   Lemma 5, p. 28 — |C(q, d)| ≤ (b∨h)D̄ for q, d ∈ [0, D̄], and the bound is attained
-- statement:
--   Let $b,h>0$ be the unit backordering and holding costs, let $\bar D\ge0$, and let $C(q;d)=b(d-q)^+ + h(q-d)^+$ be the newsvendor cost. Then for all order quantities and demands in $[0,\bar D]$,
--   $$|C(q;d)|\le (b\vee h)\,\bar D\qquad (q,d\in[0,\bar D]),$$
--   and the bound is tight: $(b\vee h)\bar D$ is the largest value of $|C(q;d)|$ over $q,d\in[0,\bar D]$.
--
--   This is the uniform bound on the loss that the generalization bound of Theorem 6 needs; applied to rules whose predictions lie in $[0,\bar D]$, it gives the constant $M=(b\vee h)\bar D$ in the proof of Theorem 2.
--
--   **Formalization Note** The printed lemma takes the supremum of $|C(q_n(x),D(x))|$ over $(x,D)\in\mathcal X\times\mathcal D$; its proof argues over $q,d\in[0,\bar D]$ and attains the bound at $(q,d)=(\bar D,0)$ and $(0,\bar D)$. The statement follows the proof's form: the predictions are taken in $[0,\bar D]$, which is what the range assumption of Appendix B guarantees.
-- source:
--   Rudin & Vahn, The Big Data Newsvendor: Practical Insights from Machine Learning, MIT Sloan Working Paper 5036-13 (version of February 6, 2014), p. 28, Lemma 5 and its proof

import Mathlib
import Definitions.Def_BigDataNV_Reg_Setting

namespace BigDataNV.Reg

/-- Lemma 5, p. 28: on `[0, D̄] × [0, D̄]` the newsvendor cost is bounded by `(b ∨ h) D̄`, and the
bound is attained. -/
theorem lemma5_cost_bound (b h Dbar : ℝ) (hb : 0 < b) (hh : 0 < h) (hD : 0 ≤ Dbar) :
    (∀ q ∈ Set.Icc 0 Dbar, ∀ d ∈ Set.Icc 0 Dbar, |nvCost b h q d| ≤ max b h * Dbar) ∧
    IsGreatest {c : ℝ | ∃ q ∈ Set.Icc 0 Dbar, ∃ d ∈ Set.Icc 0 Dbar, c = |nvCost b h q d|}
      (max b h * Dbar) := by sorry

end BigDataNV.Reg
