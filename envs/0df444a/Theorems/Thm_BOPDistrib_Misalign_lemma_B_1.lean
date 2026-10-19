-- Prove2me | Theorems.Thm_BOPDistrib_Misalign_lemma_B_1
-- name    : BOPDistrib.Misalign.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:21.111208+00:00
-- url     : https://prove2.me/theorems/f7a90dbc-4d64-460d-ab7e-e4b4f15841a9
-- title:
--   Lemma B.1, p. 47 (PDF 48) — θ^M = θ^MR ≥ θ^F ≥ θ^FR under Assumption 1
-- statement:
--   Under the standing assumptions (in particular the strict homogeneous Assumption 1), the education levels of the four strategies of Theorem 1 satisfy, for every risk aversion $\alpha>0$,
--   $$\theta^M=\theta^{MR}\ \ge\ \theta^F\ \ge\ \theta^{FR}.$$
--
--   The lemma orders the strategies by how much of the market they inform. It is the key input to the consumer-surplus comparison of Proposition 2.
--
--   **Formalization Note** $\theta^{FR}$ depends on $\alpha$ through the tie-break $\mathbb 1\{y\le y_\theta\}$.
-- source:
--   Calmon, Jue-Rajasingh, Romero & Stenson, Operational strategies for distributing durable goods in the base of the pyramid, accepted manuscript (M&SOM 24(4), 2022; TSpace, SSRN 2882402), p. 47 (PDF 48), Lemma B.1, eq. (18)

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

namespace BOPDistrib.Misalign

/-- Lemma B.1 (p. 47): under (strict, homogeneous) Assumption 1, `θ^M = θ^MR ≥ θ^F ≥ θ^FR`. -/
theorem lemma_B_1 (P : Params) (m α : ℝ) (hS : Standing P m) (hα : 0 < α) :
    thetaM P = thetaMR P ∧ thetaF P m ≤ thetaM P ∧ thetaFR P m α ≤ thetaF P m := by sorry

end BOPDistrib.Misalign
