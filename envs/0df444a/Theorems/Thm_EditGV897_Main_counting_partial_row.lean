-- Prove2me | Theorems.Thm_EditGV897_Main_counting_partial_row
-- name    : EditGV897.Main.counting_partial_row
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:27:01.337399+00:00
-- url     : https://prove2.me/theorems/eb47dd69-8539-4755-9252-9ada111c25bd
-- title:
--   Lemma 1 — Counting under a partial row
-- statement:
--   Let $t\ge1$, let $F$ be an explicitly supplied admissible family of $M\ge1$ affine length-preserving edit maps on $\mathbb F_2^n$, and let $G$ contain at most $n$ previously selected parity rows. For every partial row $p$ of length at most $n$, let $E(p)$ be the average number of surviving nonzero collision witnesses under a uniformly random completion. Fixed points do not count as witnesses.
--
--   There are fixed deterministic programs that count solutions of every supplied affine binary system, evaluate $E(p)$ exactly, and construct the specified new full row $h$ from the empty prefix, with
--
--   $$2W_{[G;h]}(\mathbb F_2^n)\le W_G(\mathbb F_2^n).$$
--
--   The computed affine counts equal solution-set cardinalities and the executable witness counts equal the indexed mathematical witness sums. The expectation evaluator returns exactly $2E(p)$, so no rounding occurs. For common uniform $A>0$ and natural degree $d$, the affine counter runs within $A(n+|E|+1)^d$ transitions on a system $E$; the expectation evaluator and row builder run within $A(n+M+1)^d$. Programs and bounds precede all dimensions, families, rows and prefixes.
--
--   This supplies the exact counting and half-separation guarantee used to construct the shared matrix. It includes zero surviving witnesses and complete prefixes.
--
--   **Formalization Note** The expectation is independently defined as a rational finite average. The affine counter is Gaussian elimination, not a counting oracle. The new row need not extend the arbitrary prefix passed to the separate evaluator.
--
--   Differences from the source:
--   - encoding: ordered binary words and one-based positions → Fin n → ZMod 2, ordered lists, and zero-based positions; reason: these are order-preserving representations of the same words and legal edits
--   - encoding: an indexed family of affine edit maps → a list with occurrence multiplicity and membership in the canonical legal-script family; reason: equal induced maps remain separately indexed and fixed-point witnesses are excluded
--   - encoding: E(p)=(T-Z_j)/2+Q_j(p) → an integer output 2E(p) and equality with twice the rational uniform-completion average; reason: multiplication by two preserves the exact expectation without rounded division
--   - encoding: deterministic polynomial-time algorithms → fixed finite binary tape programs with actual halting executions bounded by positive uniform A(s+1)^d; reason: the fixed-tape bit model preserves polynomial time and charges input, output and all arithmetic work
--   - encoding: the counting procedure invoked in the proof → explicit Gaussian-count correctness and a uniform counter realization included with the two lemma conclusions; reason: these state the procedure used in §§3.2 and 4.1 instead of assuming its correctness or efficient execution
--   - generalization: the rows already selected by Part 1 → any row list G with at most n rows; reason: the exact conditional-expectation calculation and halving argument use only the supplied rows; every Part 1 row prefix satisfies this size bound
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Lemma 1, §4.1, printed p. 10 / PDF p. 11; affine-counting interface §3.2, printed pp. 7–8 / PDF pp. 8–9

import Definitions.Def_EditGV897_Main_Construction

namespace EditGV897.Main

/-- Lemma 1, including the affine-system counting interface of §3.2.
The row starts at ε; the expectation evaluator handles every legal prefix. -/
theorem counting_partial_row :
    ∃ (counter evaluator rowBuilder : Program) (A d : ℕ), 0 < A ∧
      (∀ (n : ℕ) (E : List (Equation n)),
        affineCount E = (affineSet E).card ∧
        Runs counter (unary n ++ equationCode E) (binary (affineCount E))
          (polyBudget A d (n + E.length))) ∧
      (∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length ≤ n →
        (∀ E : List (Equation n), witnessCount F G E = witnessSum F G (affineSet E)) ∧
        (∀ p : List Bit, p.length ≤ n →
          (twiceExpectation F G p : ℚ) = 2 * expectation F G p ∧
          Runs evaluator (expectationInput F G p) (integerCode (twiceExpectation F G p))
            (polyBudget A d (n + F.length))) ∧
        2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ ∧
        Runs rowBuilder (familyRowsInput F G) (wordCode (chooseRow F G))
          (polyBudget A d (n + F.length))) := by sorry

end EditGV897.Main
