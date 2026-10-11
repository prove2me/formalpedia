-- Prove2me | Theorems.Thm_CLRS_Chapter4Publication_Strassen_correctness_and_running_time
-- name    : CLRS.Chapter4Publication.Strassen.correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:07:46.882987+00:00
-- url     : https://prove2.me/theorems/aae4fd7f-e6b3-4808-8ce6-5be6935b47f1
-- title:
--   CLRS Chapter 4, §4.2: Strassen Matrix Multiplication — Correctness and Subcubic Counted Work
-- statement:
--   ## Multiplication with seven recursive products
--
--   Strassen's algorithm replaces eight half-size matrix products with seven,
--   together with matrix additions and subtractions. This yields a subcubic
--   arithmetic bound and makes the cost of intermediate copying and combination
--   relevant to the full implementation. This result follows
--   [CLRS, fourth edition, §4.2](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/),
--   with the underlying algorithm due to
--   [Strassen](https://doi.org/10.1007/BF02165411). Its target is a reusable contract
--   for compiled source, encompassing the output, preservation, allocation,
--   termination, and measured work.
--
--   ## Nested matrices and four source clocks
--
--   The entry point is `strassen(a, b, n)`. A **nested matrix** has source type
--   `Seq[Seq[Int]]`: an outer array stores references to integer row arrays.
--   `MatrixHeap.Stored h a A` and `Stored h b B` connect valid heap references
--   to mathematical values $A,B:\mathbb Z\to\mathbb Z\to\mathbb Z$.
--   All integer-indexed row references must be valid. Repeated row references
--   within either matrix and shared references across the inputs are permitted.
--
--   The **dimension** is $n=2^k$ for natural $k\ge0$. The finite square uses
--   $0\le i,j<n$; no zero-padding condition is imposed outside it, although all
--   entries must satisfy the heap representation premise. The source copies quadrants,
--   forms the seven recursive products, combines them, and joins the four output
--   blocks. Every finite returned row has its own fresh reference.
--
--   **Counted work** $T$ sums increments of four named clocks: `products`,
--   `calls`, `linear_cells`, and `copied_cells`. They respectively count scalar
--   products at recursion leaves, recursive `strassen` calls, cells processed by
--   addition/subtraction helpers, and copied cells. The clocks begin at arbitrary
--   values; only their increments contribute to $T$.
--
--   ## Formalization targets
--
--   For every valid input, the actual compiled call terminates with a fresh result
--   matrix $R$ in a heap $h'$ satisfying
--
--   $$
--   R_{ij}=\sum_{t=0}^{n-1}A_{it}B_{tj}\quad(0\le i,j<n),
--   \qquad R_{ij}=0\quad\text{outside the square}.
--   $$
--
--   All pre-existing caller rows, outer arrays, and objects are unchanged. The
--   finite result rows are valid, fresh, and pairwise distinct. The stable runtime
--   target places its upper constant before every depth, heap, matrix, and entry value:
--
--   $$
--   \exists C\in\mathbb N_{>0}\;\forall\text{ valid inputs of size }n=2^k,
--   \qquad 7^k\le T\le C\,7^k.
--   $$
--
--   This is $\Theta(n^{\log_2 7})$ on the permitted dimensions. The checked
--   development states its bounds with natural powers $7^k$; the displayed
--   logarithmic expression is their conventional mathematical interpretation,
--   not a separate checked real-exponent theorem in these matrix files.
--
--   The exact source counters provide stronger supporting results. Define
--
--   $$
--   C_7(0)=1,\quad C_7(k+1)=1+7C_7(k),\qquad
--   H(0)=0,\quad H(k+1)=4^k+7H(k).
--   $$
--
--   Then
--
--   $$
--   \begin{aligned}
--   \Delta\mathrm{products}&=7^k,&
--   \Delta\mathrm{calls}&=C_7(k),\\
--   \Delta\mathrm{linear\_cells}&=18H(k),&
--   \Delta\mathrm{copied\_cells}&=12H(k).
--   \end{aligned}
--   $$
--
--   Every other named clock is unchanged. The total obeys
--   $T(0)=2$ and $T(k+1)=7T(k)+30\cdot4^k+1$. The development proves
--   $7^k\le T(k)\le13\cdot7^k$ for every $k$, with uniform upper witness $C=13$.
--
--   ## What the formal result supplies
--
--   `CLRS.Chapter4Publication.Strassen.correctness_and_running_time` combines
--   the actual returning call, mathematical product, preserved caller storage,
--   fresh output allocation, exact clock increments, and uniform runtime bound.
--   All these conclusions concern the same final heap.
--
--   The source execution summary supplies the returning call, preserved caller storage, fresh distinct rows, and exact counters. The value theorems identify its result with ordinary matrix multiplication, including zero outside the square. The combined headline uses the uniform upper witness 13. The source’s bundled editor theorem also contains a weaker valid upper bound of 33; the headline’s supporting cost bound establishes the sharper constant.
--
--   ## Where the specification needs care
--
--   The seven-product algebraic identity does not by itself describe allocation,
--   shared references, copying, or counter changes. All these operations must agree
--   with the returned matrix in the same compiled execution. A bound only on leaf
--   products would also omit the cell-processing work used to create and join
--   intermediate matrices.
--
--   ## Formalization scope and algorithm source
--
--   Inputs contain arbitrary unbounded integers. The theorem assumes positive
--   power-of-two size; it supplies no claim for zero, unsupported dimensions,
--   rectangles, or automatic padding. `products` counts only recursive leaf
--   products. The helper expression `sign * b[i]` is accounted for by
--   `linear_cells`, so $7^k$ is not a count of every multiplication operator in the
--   source. Allocation, uncharged loop bookkeeping, wall-clock time, integer bit
--   complexity, and exact generated transition counts are outside $T$.
--
--   The exact standalone algorithm is
--   [`examples/matrix_strassen.algo`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/matrix_strassen.algo).
--   The bundled proof is
--   [`examples/analysis/matrix_strassen.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/analysis/matrix_strassen.lean).
--   The modular proof entry points are
--   [`StrassenTheorems.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/StrassenTheorems.lean)
--   and
--   [`RecurrenceApplications.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/RecurrenceApplications.lean).
--   The compiler identity is development commit
--   `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41` from
--   `chutongyang98/Lean_formalization`, branch `codex/clrs-chapter-4`, with Lean
--   4.26.0; these results do not claim generation by public v0.1.4. The proofs
--   are handwritten analyses of generated definitions. Exact reproduction does not prove the compiler correct. Algo2Lean was created by Lunjia Hu;
--   Chutong Yang is a contributor, and both are software citation authors.
--   Alternative proofs
--   must retain the compiled algorithm, all valid represented inputs, actual
--   termination, and this four-clock model.
--
--   ## Selected references
--
--   - Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
--     *Introduction to Algorithms*, fourth edition, MIT Press, 2022, Chapter 4,
--     §4.2, with §§4.3–4.4 for the recurrence methods.
--     [Publisher](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/).
--   - Volker Strassen, “Gaussian elimination is not optimal,” *Numerische
--     Mathematik* **13**, 354–356, 1969.
--     [DOI: 10.1007/BF02165411](https://doi.org/10.1007/BF02165411).
--   - Algo2Lean Chapter 4 development, commit
--     `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, 2026.
--     [Scope and theorem guide](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/docs/CLRS_CHAPTER_4.md).
--
--   **Formalization Note.** The submitted headline is
--   `CLRS.Chapter4Publication.Strassen.correctness_and_running_time`, from
--   the [combined contracts](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Publication/MatrixContracts.lean).
--   It places the positive natural runtime constant before all input heaps, references,
--   values, and dimensions. The actual returning call, mathematical product, storage
--   preservation, fresh outer array, distinct fresh finite rows, exact clock increments,
--   and runtime inequalities are conjuncts about the same final heap. The source
--   repository pins Lean 4.26.0; this upload is checked in the separate Lean 4.33.1,
--   Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` environment. The compiler is the development snapshot
--   `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, not public Algo2Lean v0.1.4.
--
--   **Platform namespace.** The imported Chapter 4 source declarations live under `CLRS` in this upload to avoid collisions with independently published compiler versions. The immutable source reference retains the original declaration names.
-- source:
--   Algo2Lean Chapter 4 development, declaration Chapter4Publication.Strassen.correctness_and_running_time, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Publication/MatrixContracts.lean#L209-L232

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiply
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursive
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursiveGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassen
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_CallCost
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
import Definitions.Def_CLRS_Chapter4_Publication_MatrixContracts
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS
end CLRS
open CLRS
open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap
namespace CLRS.Chapter4Publication
end CLRS.Chapter4Publication
open CLRS.Chapter4Publication
namespace CLRS.Chapter4Publication.Strassen
end CLRS.Chapter4Publication.Strassen
open CLRS.Chapter4Publication CLRS.Chapter4Publication.Strassen

theorem CLRS.Chapter4Publication.Strassen.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixStrassenLibrary.strassen.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (product (2^depth) av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixStrassenExecution.costs depth) ∧
          7^depth ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*7^depth := by sorry
