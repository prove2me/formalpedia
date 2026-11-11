-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_observation_6_4
-- name    : ApproxCountRwPHP.Unprovability.observation_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:52.658655+00:00
-- url     : https://prove2.me/theorems/86df2bfb-764d-403c-aa3f-3a5d6a3ab40c
-- title:
--   Observation 6.4 — freshness is preserved
-- statement:
--   Fix a finite function signature of maximum arity a and an infinite structure on U. Choose an N-element subset S of U and an enumeration of it. Let (π,μ) be a fresh state and T a decision tree satisfying
--
--   $$|\pi|+(a+1)\operatorname{height}(T)\le N.$$
--
--   For every extension π′⊇π with μ[T^ω(π)=π′]>0, conditioning μ on this event leaves a fresh state:
--
--   $$(\pi',\mu[\,\cdot\mid T^\omega(\pi)=\pi'])\text{ is fresh}.$$
--
--   This retains both the extension requirement and positive conditioning probability. No global independence is demanded of orders at already matched coordinates.
--
--   Differences from the source:
--   - generalization: decision trees in the fixed formula and infinite countermodel setting of §6.1 → any finite function signature and any infinite structure; reason: freshness and order swapping depend only on the primitive function interpretations, not the countermodel property; the original setting is a specialization
--   - encoding: priority orders, partial injections, and real event probabilities → finite permutations, optional partial maps with injection in freshness, product measures, and ENNReal probabilities; reason: the bounds ensure traversal succeeds; probabilities agree with their real values, and conditioning is used only on a positive-probability event
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Observation 6.4, printed p. 37, PDF p. 39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=39

import Definitions.Def_ApproxCountRwPHP_Unprovability_Priorities

open MeasureTheory

namespace ApproxCountRwPHP.Unprovability

/-- Observation 6.4, printed 37 / PDF 39. Positive event probability is
required before conditioning, with the same weak size inequality. -/
theorem observation_6_4 (S : Signature) (N : ℕ) (U : Type) [S.language.Structure U]
    [Infinite U] (σ : Fin N ↪ U) (π π' : PartialMap N U)
    (μ : Measure (PriorityOracle N U)) (hfresh : fresh π μ)
    (T : DecisionTree S N) (hsize : mapSize π + (maximumArity S + 1) * treeHeight T ≤ N)
    (hext : extendsMap π' π)
    (hpositive : 0 < μ {ω | traversalMap σ ω T π = some π'}) :
    fresh π' (ProbabilityTheory.cond μ {ω | traversalMap σ ω T π = some π'}) := by sorry

end ApproxCountRwPHP.Unprovability
