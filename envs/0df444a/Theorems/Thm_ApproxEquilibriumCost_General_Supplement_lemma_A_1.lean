-- Prove2me | Theorems.Thm_ApproxEquilibriumCost_General_Supplement_lemma_A_1
-- name    : ApproxEquilibriumCost.General.Supplement.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:47:29.993007+00:00
-- url     : https://prove2.me/theorems/90f94379-f1e6-4f8d-9ae7-8f3e620a3f49
-- title:
--   Lemma A.1 (used in the proof of Theorem 4.2) — continuity, strict increase and exact image
-- statement:
--   For every integer $d\ge1$, the function $\lambda_d(x)=\frac{x}{1+x}(1-(1+x)^{-1/d})$ satisfies all three assertions:
--
--   $$\lambda_d\text{ is continuous on }[0,\infty),\qquad
--   \lambda_d\text{ is strictly increasing on }[0,\infty),\qquad
--   \lambda_d([0,\infty))=[0,1).$$
--
--   The exact image includes both containment and surjectivity. These properties justify the inverse function used in Theorem 4.2.
--
--   Differences from the source:
--   - encoding: integer d ≥ 1 → natural d with 1 ≤ d and real fractional powers; reason: this is the same degree domain, with real rather than truncated natural division
-- source:
--   Yu Cheng, Tianle Jiang, STOC 2027 submission #438 (October 2026), How Much Can Approximate Equilibria Change the Social Cost of Selfish Routing?, Lemma A.1, printed p.27 = PDF p.27 (offset 0). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/438.pdf

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_UpperParameters

namespace ApproxEquilibriumCost.General.Supplement

/-- Lemma A.1, printed/PDF p.27. Continuity, strict increase, and
exact image (surjectivity as well as inclusion). -/
theorem lemma_A_1 (d : ℕ) (hd : 1 ≤ d) :
    ContinuousOn (lambda d) (Set.Ici 0) ∧
    StrictMonoOn (lambda d) (Set.Ici 0) ∧
    (lambda d) '' Set.Ici 0 = Set.Ico 0 1 := by sorry

end ApproxEquilibriumCost.General.Supplement
