-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_bledsoe_claim
-- name    : DROOptimal.Prescriptor.bledsoe_claim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:01.695985+00:00
-- url     : https://prove2.me/theorems/ec9836b5-f6b0-4f7f-99a7-6fbd733a4f1e
-- title:
--   Proof of Theorem 7, p. 21 — a quasi-continuous prescriptor is continuous on a dense subset of 𝒫
-- statement:
--   Let $\mathcal P$ be the probability simplex on $\{1,\dots,d\}$ with its subspace topology, $X\subseteq\mathbb R^n$ any set, and $\hat x:\mathcal P\to X$ a quasi-continuous function. Then the set of points at which $\hat x$ is continuous is dense in $\mathcal P$:
--   $$
--   \overline{\{\mathbb P'\in\mathcal P : \hat x \text{ is continuous at } \mathbb P'\}}=\mathcal P .
--   $$
--
--   The paper cites this from Bledsoe (1952) and uses it in the proof of Theorem 7 to move the point where a competing pair beats the distributionally robust pair to a point of continuity of the competing prescriptor. On p. 7 the same fact is phrased as: the discontinuity points of a quasi-continuous prescriptor form a meagre set, and by the Baire category theorem the continuity points are dense.
--
--   **Formalization Note** The compactness of $X$ assumed throughout the paper is not needed and is not assumed.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 21, proof of Theorem 7 (citing Bledsoe 1952); also p. 7, after Definition 3

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Proof of Theorem 7, p. 21 (Bledsoe 1952; also p. 7 after Definition 3): a quasi-continuous
prescriptor x̂ : 𝒫 → X is continuous on a dense subset of 𝒫. -/
theorem bledsoe_claim {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (xhat : DROOptimal.Predictor.Δ d → ↥X)
    (hxhat : QuasiContinuous xhat) :
    Dense {ℙ' : DROOptimal.Predictor.Δ d | ContinuousAt xhat ℙ'} := by sorry

end DROOptimal.Prescriptor
