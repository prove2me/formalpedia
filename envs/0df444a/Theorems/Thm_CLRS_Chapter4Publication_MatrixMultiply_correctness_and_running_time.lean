-- Prove2me | Theorems.Thm_CLRS_Chapter4Publication_MatrixMultiply_correctness_and_running_time
-- name    : CLRS.Chapter4Publication.MatrixMultiply.correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:07:44.406684+00:00
-- url     : https://prove2.me/theorems/298e6415-527e-4019-bfa4-9ffb9087db34
-- title:
--   CLRS Chapter 4, §4.1: Ordinary Matrix Multiplication — Correctness and Cubic Counted Work
-- statement:
--   ## Reusable matrix multiplication
--
--   Matrix multiplication combines the rows of one matrix with the columns of
--   another. A program calling it needs more than the familiar formula: the call
--   must finish, the returned storage must contain that formula, and existing
--   data must survive. This result connects the ordinary row–column–inner-index
--   algorithm of [CLRS, fourth edition, Chapter 4](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)
--   to those guarantees for its compiled Algo2Lean execution.
--
--   ## Matrices, references, and counted work
--
--   A **matrix** is a finite square within an array of integer row arrays,
--   `Seq[Seq[Int]]`. The size is a natural number $n$, including zero. Mathematical
--   values $A,B:\mathbb Z\to\mathbb Z\to\mathbb Z$ describe the inputs; only
--   coordinates $0\le i,j<n$ belong to the multiplication problem. No zero-padding
--   condition is imposed outside that square; all values remain subject to the
--   heap representation condition below.
--
--   A **heap** stores the outer arrays, row arrays, objects, and named counters.
--   `MatrixHeap.Stored h a A` means that `a` is a valid outer-array reference and
--   every integer-indexed row reference is allocated with the specified values.
--   Input rows may share references, including across the two matrices, and the
--   two matrix references may coincide. Shared references necessarily have
--   consistent values. No input separation assumption is imposed.
--   The finite supply of allocated row identifiers permits only finitely many
--   distinct whole row sequences across all integer row indices. This
--   representation premise remains required when $n=0$.
--
--   The entry point is `matrix_multiply(a, b, n)`. **Counted work** $T$ is the
--   increment of the `multiply_add` clock. One unit covers one scalar
--   multiplication together with its accumulation into a dot product. Arithmetic
--   uses unbounded mathematical integers.
--
--   ## Formalization targets
--
--   For every valid initial heap and represented pair of inputs, establish a
--   terminating compiled call returning a fresh matrix $R$ in a final heap $h'$:
--
--   $$
--   R_{ij}=\sum_{t=0}^{n-1}A_{it}B_{tj}\quad(0\le i,j<n),
--   \qquad R_{ij}=0\quad\text{outside the square}.
--   $$
--
--   The same call preserves all previously allocated rows, outer arrays, and
--   objects. Its finite output rows are allocated separately and are pairwise
--   distinct. The stable runtime target uses an upper constant quantified before every
--   size, heap, matrix reference, and input value:
--
--   $$
--   \exists C\in\mathbb N_{>0}\;\forall\text{ valid inputs},\quad
--   n^3\le T\le C n^3.
--   $$
--
--   The existing development proves the stronger identity $T=n^3$, with every
--   other clock unchanged, so $C=1$ works uniformly, including at $n=0$.
--   The contract includes existence of a returning execution; a statement merely
--   conditional on a return would not supply termination.
--
--   ## What the formal result supplies
--
--   `CLRS.Chapter4Publication.MatrixMultiply.correctness_and_running_time` combines
--   the actual returning call, mathematical product, preserved caller storage,
--   fresh output allocation, exact clock increments, and uniform runtime bound.
--   All these conclusions concern the same final heap.
--
--   The source execution summary and completed-run theorems supply exact product values, storage preservation, costs, and distinct finite row identities. A caller can reuse the contract without repeating the dot-product analysis; fresh independent result rows support subsequent mutation of one row without changing another or either input.
--
--   ## Where the specification needs care
--
--   Equal matrix values do not determine heap aliasing. In particular,
--   `const(const(0))` initially repeats one zero-row reference; independently
--   writable output rows require additional allocations. A pure matrix identity
--   alone would miss this obligation and would not establish that the source
--   loops terminate or charge the stated counters.
--
--   ## Formalization scope and algorithm source
--
--   The square may be empty. Rectangular multiplication, negative size arguments,
--   and malformed references are outside this contract. The arrays themselves
--   are total over integer indices, not finite machine buffers. Preservation is
--   `MatrixHeap.Extends h h'`; it covers every previously allocated caller object,
--   not only the two inputs. Work excludes allocation, loop bookkeeping, elapsed
--   time, integer bit complexity, and uninstrumented generated transitions.
--
--   The exact standalone source is
--   [`examples/matrix_multiply.algo`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/matrix_multiply.algo).
--   The corresponding proof is
--   [`examples/analysis/matrix_multiply.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/analysis/matrix_multiply.lean).
--   Both use the shared
--   [`Algo2LeanLib/MatrixHeap.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/Algo2LeanLib/MatrixHeap.lean)
--   representation. Alternative proofs must retain the compiled call, unrestricted
--   valid input data, and the same tick model.
--
--   **Provenance.** Use Algo2Lean development commit
--   `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41` from
--   `chutongyang98/Lean_formalization`, branch `codex/clrs-chapter-4`, with Lean
--   4.26.0. The proof is handwritten analysis of generated definitions. This is
--   not the public v0.1.4 compiler. Reproducing generation does not prove the compiler correct. Algo2Lean was created by Lunjia Hu; Chutong Yang is
--   a contributor, and both are software citation authors.
--
--   ## Selected references
--
--   - Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest, and Clifford Stein,
--     *Introduction to Algorithms*, fourth edition, MIT Press, 2022, Chapter 4,
--     §4.1. [Publisher](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/).
--   - Algo2Lean Chapter 4 development, commit
--     `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, 2026.
--     [Scope and theorem guide](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/docs/CLRS_CHAPTER_4.md).
--
--   ---
--
--   **Formalization Note.** The submitted headline is
--   `CLRS.Chapter4Publication.MatrixMultiply.correctness_and_running_time`, from
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
--   Algo2Lean Chapter 4 development, declaration Chapter4Publication.MatrixMultiply.correctness_and_running_time, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Publication/MatrixContracts.lean#L83-L137

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
namespace CLRS.Chapter4Publication.MatrixMultiply
end CLRS.Chapter4Publication.MatrixMultiply
open CLRS.Chapter4Publication CLRS.Chapter4Publication.MatrixMultiply

theorem CLRS.Chapter4Publication.MatrixMultiply.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (n : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixMultiplyLibrary.matrix_multiply.Call heap (a, b, (n : Int)) after result ∧
          Stored after result (product n av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result n ∧
          heap.Increments after (MatrixMultiplyAnalysis.costs n) ∧
          n^3 ≤ runtime (heap.cost after) ∧ runtime (heap.cost after) ≤ C*n^3 := by sorry
