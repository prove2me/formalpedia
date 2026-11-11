-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_theorem_1_5
-- name    : ApproxCountRwPHP.Unprovability.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:23.494194+00:00
-- url     : https://prove2.me/theorems/e7766f09-3204-41df-b73e-e9514fed8111
-- title:
--   Theorem 1.5 — APX1(f,g) does not prove rwPHP(f,g)
-- statement:
--   Let the language contain all bounded polynomial-time oracle programs for f, g, and P. The oracles f and g have lengths |f(u)|=|u|−1 and |g(v)|=|v|+1, with subtraction truncated at zero. Let A be the universal standard base for arbitrary length-bounded oracles together with exactly the Basic, Boundary, Precision Consistency, and Local Consistency counting axioms. Then
--
--   $$A\not\models\forall u\ \exists x\ (|x|=|u|\land (|f(x)|\ge|u|\lor g(f(x))\ne x)).$$
--
--   This strengthens the printed theorem only at the base theory. By first-order completeness it states unprovability. The theorem has no hypotheses: the language, theory, and sentence are all concretely defined. Correct counting is not a hypothesis in the definition of A.
--
--   Differences from the source:
--   - reading: Remark 1.4 and §5.1 give a numeric form, whereas equation (3.2) gives a string form → equation (3.2) with the two exact oracle length axioms of §3.2; reason: the mission brief fixes this reading; those argument-uniform length axioms belong to the string formulation
--   - generalization: the relativized PV1 base → all universal sentences true in every standard interpretation with the stated oracle length bounds; reason: this contains the PV1 axioms; the standard-interpretation argument on PDF 45 still applies to every such base axiom, without requiring counting correctness
--   - encoding: first-order derivability with equality → semantic consequence and validity in Mathlib; reason: Gödel completeness identifies these notions for the source statements
--   - encoding: binary strings, rational values, and δ⁻¹∈Log → List Bool with leading zeros, value-based rational equality, and nonempty strings for defined positive precision reciprocals; reason: efficient encodings preserve all source values; zero-length precisions do not denote a defined positive reciprocal, while the rwPHP zero-length instance is retained
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Theorem 1.5; theory §3.2 and equation (3.2), printed p. 4, 18–19, PDF p. 6, 20–21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=6, 20–21

import Definitions.Def_ApproxCountRwPHP_Unprovability_APX

namespace ApproxCountRwPHP.Unprovability

/-- Theorem 1.5, printed 4 / PDF 6, with the §3.2 / eq. (3.2) string reading.
The base is strengthened to universal truths for arbitrary length-bounded
oracles. Counting is still governed by exactly the four syntactic axioms.
Semantic nonconsequence represents first-order unprovability by completeness. -/
theorem theorem_1_5 : ¬ (APX1fg ⊨ᵇ rwPHPfg) := by sorry

end ApproxCountRwPHP.Unprovability
