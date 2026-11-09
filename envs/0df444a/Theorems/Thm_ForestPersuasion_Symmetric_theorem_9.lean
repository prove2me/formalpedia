-- Prove2me | Theorems.Thm_ForestPersuasion_Symmetric_theorem_9
-- name    : ForestPersuasion.Symmetric.theorem_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:19:37.184022+00:00
-- url     : https://prove2.me/theorems/e4ee051d-b5db-4de2-a9b5-290cd5912d51
-- title:
--   Theorem 9 — exact weakly polynomial computation of the sender optimum
-- statement:
--   Consider all forest persuasion instances with full-support binary prior, receiver utilities satisfying the standing sign conditions, and monotone nonnegative symmetric sender utility $u(S)=f(|S|)$. Numerical inputs are rational and encoded in binary. There exist a single function $g$ and a single Turing machine with a polynomial time bound, valid uniformly over all such instances $I$, satisfying
--   $$g(I)\in\mathbb Q,\qquad g(I)=V^*(I),\qquad\operatorname{time}(I)\le P(|\operatorname{encode}(I)|).$$
--   Here $V^*$ is defined from actual schemes over arbitrary signal alphabets. The attained-value set is nonempty and bounded above as part of the conclusion. There is no restriction on receiver count, hierarchy depth, denominator size, or the shape of the monotone function $f$. The output is exact, with no approximation parameter. This is the full algorithmic claim of Theorem 9.
--
--   Differences from the source:
--   - encoding: receivers 1,...,n and a directed forest → Fin n and an acyclic optional-parent map; reason: a relabelling of the same finite rooted forests; receiver i observes every coordinate in its reflexive descendant set
--   - generalization: n receivers with n implicitly positive → n may also be zero; reason: with no receivers all vertex-indexed identities are vacuous; every positive-size instance is retained
--   - reading: distributions over an abstract signal set → PMFs over arbitrary M : Type, with no finite-support or cardinality bound; reason: the Bayes formula uses point masses and Appendix B footnote 6 explicitly works with discrete distributions; Lemma 5 attains the same optimum with finite support
--   - encoding: Bayes posteriors and expected sender utility → zero posterior on zero-mass observations, ENNReal nonnegative expectations converted to real; reason: full-support prior makes such observations null in both states, and finite-domain sender utilities make all expectations finite
--   - encoding: the maximum V* over inducible information structures → the real supremum over values of actual schemes, with nonempty and bounded guards as conclusions; reason: a constant scheme is available and all utilities are bounded; Lemma 5 supplies attainment, so the supremum has the stated maximum value
--   - reading: real-valued numerical data and weakly polynomial-time computation → rational prior, four rational payoffs per receiver and a nonnegative rational f table, encoded in binary; reason: weak polynomial time is interpreted in the standard rational bit model; no numerator or denominator bound is imposed, and the symmetric oracle requires only n+1 table values
--   - encoding: a weakly polynomial-time algorithm → Nonempty (Turing.TM2ComputableInPolyTime encodeInstance encodeRat g), for one g before all inputs; reason: Mathlib supplies one TM2 machine and one polynomial in input bit length, using Bool input and output alphabets; validity proofs are erased from the encoding
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), Theorem 9, PDF p. 12 (printed p. 11), proof PDF pp. 12–15 (printed pp. 11–14). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ForestPersuasion_Symmetric_Encoding

open scoped NNReal ENNReal

namespace ForestPersuasion.Symmetric

/-- Theorem 9, PDF p. 12, STOC 2027 submission #271.
Reading: finite numerical inputs are rational in binary, as required by weak polynomial time.
One function and one polynomial-time machine work on every valid forest instance.
The structural supremum guards are conclusions, never assumptions about an oracle or an LP. -/
theorem theorem_9 :
    ∃ g : Instance → ℚ,
      Nonempty (Turing.TM2ComputableInPolyTime encodeInstance encodeRat g) ∧
      ∀ I : Instance,
        (attainableValues I.val.model I.utility).Nonempty ∧
        BddAbove (attainableValues I.val.model I.utility) ∧
        (g I : ℝ) = Vstar I.val.model I.utility := by sorry

end ForestPersuasion.Symmetric
