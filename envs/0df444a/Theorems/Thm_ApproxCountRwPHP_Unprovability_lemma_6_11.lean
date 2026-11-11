-- Prove2me | Theorems.Thm_ApproxCountRwPHP_Unprovability_lemma_6_11
-- name    : ApproxCountRwPHP.Unprovability.lemma_6_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:02:12.229493+00:00
-- url     : https://prove2.me/theorems/87ba01af-dc02-4c20-91e5-b7358011c28c
-- title:
--   Lemma 6.11 — proofs yield winning inspectors (powers of two)
-- statement:
--   Let L be a finite function-and-constant signature and φ a quantifier-free formula with k variable positions. Let A(L̂) use the parameterized language with only the stated primitive length bounds, the universal standard base, and all four counting axioms. If A(L̂) entails Θφ at every power-of-two size 2^{|u|}, then there exists a polynomial Q with natural coefficients such that, for every n≥1, Q(n)≥1 and the inspector has a winning adaptive strategy in
--
--   $$G_\phi(2^n;Q(n),Q(n),1/Q(n)).$$
--
--   The polynomial is chosen before n and may depend on the proof. Its positivity ensures a legal game precision. The powers-of-two premise is the generalization needed by the fixed string reading of the goal.
--
--   Differences from the source:
--   - generalization: provability of Θφ at every positive size → semantic consequence only of Θφ at powers of two; reason: the base proves Θφ implies its powers-of-two restriction, and the source inspector construction uses only size 2^n
--   - generalization: the relativized PV1 base → all universal sentences true in every standard interpretation with the stated oracle length bounds; reason: this contains the PV1 axioms; the standard-interpretation argument on PDF 45 still applies to every such base axiom, without requiring counting correctness
--   - encoding: first-order derivability with equality → semantic consequence and validity in Mathlib; reason: Gödel completeness identifies these notions for the source statements
--   - generalization: a finite function-and-constant language L with exactly k free variables → an enumerated finite signature with constants at arity zero and k available variable slots, possibly unused; reason: every source instance is retained; unused coordinates can be omitted at nonempty game sizes, and at size zero extra coordinates only preclude witnesses
--   - encoding: an integer-valued polynomial resource bound Q(n) → Q in Polynomial ℕ, with Q(n)≥1 for n≥1; reason: the proof permits a positive polynomial upper bound with natural coefficients and padding unused rounds
--   - encoding: natural-number sizes and finite domains [N] in the finitary translation → canonical shortest binary numerals for sizes, bounded variables, and closed-slice outputs; arbitrary strings for the parameter u of 2^{|u|}; reason: numeral and number identify the guarded domain with exactly {0,...,N-1}; leading-zero strings remain legitimate strings but do not create extra numerical elements
--   - encoding: binary strings, rational values, and δ⁻¹∈Log → List Bool with leading zeros, value-based rational equality, and nonempty strings for defined positive precision reciprocals; reason: efficient encodings preserve all source values; zero-length precisions do not denote a defined positive reciprocal, while the rwPHP zero-length instance is retained
--   - encoding: RDTs on finite trees and three game win conditions → PMFs with a structural support-height bound and adaptive history functions; reason: bounded height over finite queries and answers implies finite support; singleton PMFs and half-mixture equality are exact
-- source:
--   Oliver Korten, Jiatu Li, Igor Oliveira, Hanlin Ren, STOC 2027 submission #1023 (October 2026), Lemma 6.11, printed p. 41, PDF p. 43; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1023.pdf#page=43

import Definitions.Def_ApproxCountRwPHP_Unprovability_Translation
import Definitions.Def_ApproxCountRwPHP_Unprovability_Game

namespace ApproxCountRwPHP.Unprovability

/-- Lemma 6.11, printed 41 / PDF 43. The powers-of-two premise generalizes
the source's premise at all sizes; Q is chosen before n. -/
theorem lemma_6_11 (S : Signature) (k : ℕ) (φ : S.language.BoundedFormula Empty k)
    (hφ : φ.IsQF) (hproof : APX1Lhat S ⊨ᵇ ThetaPow2 φ) :
    ∃ Q : Polynomial ℕ, ∀ n : ℕ, 1 ≤ n →
      1 ≤ Q.eval n ∧
      inspectorWins (N := 2^n) (h := Q.eval n) φ (Q.eval n) (1 / ((Q.eval n : ℕ) : ℝ)) := by sorry

end ApproxCountRwPHP.Unprovability
