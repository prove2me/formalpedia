-- Prove2me | Theorems.Thm_ComputationalLearning_three_cnf_pac_learnable
-- name    : ComputationalLearning.three_cnf_pac_learnable
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T03:00:48.414985+00:00
-- url     : https://prove2.me/theorems/3aea1b24-21d5-4f32-8e48-5b67c22f0119
-- title:
--   Theorem 1.4: 3-CNF formulae are PAC learnable by elimination over the (2n)³ expanded variables, with a 3-CNF hypothesis
-- statement:
--   **Theorem 1.4.** The representation class of 3-CNF formulae is efficiently PAC learnable.
--
--   Formally: let $N = (2n)^3$ be the number of triples of literals. For every target 3-CNF formula $F$ over $x_1, \dots, x_n$, every distribution $D$ on $\{0,1\}^n$, $\epsilon > 0$, $0 < \delta < 1$ and $m \ge (2N/\epsilon)(\ln 2N + \ln(1/\delta))$: the hypothesis of the algorithm of §1.5 (elimination on the expanded sample, evaluated on the expansion of the input) is consistent with every sample labeled by $F$; it is itself a 3-CNF formula (a retained negated variable $\neg y_{u,v,w}$ expands to the three unit clauses $\neg u, \neg v, \neg w$); its error exceeds $\epsilon$ with probability at most $\delta$; and 3-CNF formulae are PAC learnable using 3-CNF formulae. The bound is Theorem 1.2's over the $N$ expanded variables, transported along the one-to-one expansion of instances (p. 24).
-- source:
--   Kearns and Vazirani, An Introduction to Computational Learning Theory, MIT Press 1994, doi:10.7551/mitpress/3897.001.0001, §1.5 pp. 22-24 (the expansion y_{u,v,w} and the reduction to conjunctions) and Theorem 1.4, p. 24

import Definitions.Def_ComputationalLearning_PAC

open MeasureTheory

namespace ComputationalLearning

/-- **Theorem 1.4** (p. 24). The representation class of 3-CNF formulae is (efficiently) PAC
learnable, by running the elimination algorithm over the `(2n)³` expanded variables
`y_{u,v,w} = u ∨ v ∨ w`: for every target 3-CNF formula `F`, every distribution `D` on `{0,1}ⁿ`
and `ε, δ > 0`, the hypothesis is consistent with every sample labeled by `F`, is itself a 3-CNF
formula, and with `m ≥ (2N/ε)(ln(2N) + ln(1/δ))` examples, `N = (2n)³`, has error greater than
`ε` with probability at most `δ` (the transformation of instances is one-to-one, so the error
is preserved, p. 24); hence 3-CNF formulae are PAC learnable using 3-CNF formulae. -/
theorem three_cnf_pac_learnable {n : ℕ} (F : ThreeCNF n) (D : Measure (Cube (Fin n)))
    [IsProbabilityMeasure D] {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (m : ℕ)
    (hm : 2 * (Fintype.card (Clause n) : ℝ) / ε *
      (Real.log (2 * Fintype.card (Clause n)) + Real.log (1 / δ)) ≤ m) :
    (∀ S : Fin m → Cube (Fin n) × Bool, IsLabeledBy (evalThreeCNF F) S →
      IsConsistent (learnThreeCNF S) S) ∧
    (∀ S : Fin m → Cube (Fin n) × Bool, learnThreeCNF S ∈ threeCNFClass n) ∧
    sampleLaw D (evalThreeCNF F) m {S | ε < errorOf D (evalThreeCNF F) (learnThreeCNF S)} ≤
      ENNReal.ofReal δ ∧
    PACLearnable (threeCNFClass n) (threeCNFClass n) := by sorry

end ComputationalLearning
