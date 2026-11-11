-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_lemma_6_5
-- name    : ApproxCountRwPHP.Unprovability.lemma_6_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:43.861243+00:00
-- url     : https://prove2.me/theorems/099f1988-b076-4b28-a02b-a1a73c2aa0f4
-- title:
--   Lemma 6.5 — swapping orders
-- statement:
--   Fix an infinite structure in a finite signature whose maximum arity is a, an N-element subset of its universe, and a fresh state (π,μ). Let T₁,T₂ have heights at most h₁,h₂. If |π|+(a+1)(h₁+h₂)<N, then
--
--   $$\Pr_{\omega\sim\mu}[(T_1\circ T_2)^\omega(\pi)\ne(T_2\circ T_1)^\omega(\pi)]\le\frac{2(a+1)^2h_1h_2}{N-|\pi|-(a+1)(h_1+h_2)}.$$
--
--   The denominator is a positive real number by the strict size assumption. The comparison is of final partial injections; leaf bits play no role in composition. Zero heights remain allowed.
--
--   Differences from the source:
--   - generalization: decision trees in the fixed formula and infinite countermodel setting of §6.1 → any finite function signature and any infinite structure; reason: freshness and order swapping depend only on the primitive function interpretations, not the countermodel property; the original setting is a specialization
--   - encoding: priority orders, partial injections, and real event probabilities → finite permutations, optional partial maps with injection in freshness, product measures, and ENNReal probabilities; reason: the bounds ensure traversal succeeds; probabilities agree with their real values, and conditioning is used only on a positive-probability event
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Lemma 6.5, printed p. 37, PDF p. 39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=39

import Definitions.Def_ApproxCountRwPHP_Unprovability_Priorities

open MeasureTheory

namespace ApproxCountRwPHP.Unprovability

/-- Lemma 6.5, printed 37 / PDF 39. Every subtraction in the denominator is
in ℝ, and the strict size hypothesis makes this denominator positive. -/
theorem lemma_6_5 (S : Signature) (N : ℕ) (U : Type) [S.language.Structure U]
    [Infinite U] (σ : Fin N ↪ U) (π : PartialMap N U)
    (μ : Measure (PriorityOracle N U)) (hfresh : fresh π μ)
    (T₁ T₂ : DecisionTree S N) (h₁ h₂ : ℕ)
    (hheight₁ : treeHeight T₁ ≤ h₁) (hheight₂ : treeHeight T₂ ≤ h₂)
    (hsize : mapSize π + (maximumArity S + 1) * (h₁ + h₂) < N) :
    μ {ω | traversalMap σ ω (treeCompose T₁ T₂) π ≠ traversalMap σ ω (treeCompose T₂ T₁) π} ≤
      ENNReal.ofReal (2 * ((maximumArity S : ℝ) + 1)^2 * h₁ * h₂ /
        ((N : ℝ) - mapSize π - ((maximumArity S : ℝ) + 1) * (h₁ + h₂))) := by sorry

end ApproxCountRwPHP.Unprovability
