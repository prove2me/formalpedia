-- Prove2me | Theorems.Thm_CLRS_Chapter4Publication_MatrixRecursive_correctness_and_running_time
-- name    : CLRS.Chapter4Publication.MatrixRecursive.correctness_and_running_time
-- status  : Proved
-- author  : @Chutong
-- created : 2026-10-11T05:07:41.830656+00:00
-- url     : https://prove2.me/theorems/5829c770-8686-4265-ab93-e6cd82e6f45e
-- title:
--   CLRS Chapter 4, §4.1: Eight-Way Recursive Matrix Multiplication — Correctness and Cubic Counted Work
-- statement:
--   ## Reusable divide-and-conquer multiplication
--
--   Dividing matrix multiplication into smaller multiplications changes the
--   execution structure without changing its mathematical result. The eight-way
--   recursive algorithm in [CLRS, fourth edition, Chapter 4](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/)
--   provides a concrete setting for relating a recursive cost recurrence to actual
--   source calls. The formal result supplies matrix correctness, termination,
--   preservation, fresh result rows, and a uniform cubic bound in one execution.
--
--   ## Matrices, valid sizes, and measured operations
--
--   The inputs are **nested matrices**, `Seq[Seq[Int]]`, represented in an arbitrary
--   heap $h$ by references $a,b$ and mathematical values $A,B$. The predicate
--   `MatrixHeap.Stored` requires a valid outer array and valid row references at
--   every integer outer index. Rows may alias within or between inputs. The finite
--   problem occupies $[0,n)\times[0,n)$; no zero-padding condition is imposed outside
--   it, but those entries must also satisfy the heap representation premise.
--
--   The entry point is `matrix_recursive(a, b, n)`, with **dimension** $n=2^k$ for
--   a natural depth $k\ge0$. Thus $n\ge1$. It allocates a zero result matrix and
--   uses `matrix_block` to accumulate products into its disjoint fresh rows.
--   Row, column, and inner-coordinate offsets select submatrices of the original
--   inputs rather than creating copies of every quadrant.
--
--   Let $M$ be the increment of `multiplications` and $N$ the increment of `calls`.
--   The first counts scalar products at leaves; the second counts invocations of
--   `matrix_block`, including scalar leaves. **Counted work** is $T=M+N$, with
--   unit weight on each clock.
--
--   ## Formalization targets
--
--   For every valid heap and input pair, establish a terminating compiled call
--   returning a fresh $R$ and a final heap $h'$ with
--
--   $$
--   R_{ij}=\sum_{t=0}^{n-1}A_{it}B_{tj}\quad(0\le i,j<n),
--   \qquad R_{ij}=0\quad\text{outside the square}.
--   $$
--
--   All previously allocated caller rows, arrays, and objects remain unchanged;
--   the finite output rows are fresh and pairwise distinct. The stable cost target
--   quantifies its upper constant before every depth, heap, and input:
--
--   $$
--   \exists C\in\mathbb N_{>0}\;\forall\text{ valid inputs of size }n=2^k,
--   \qquad n^3\le T\le C n^3.
--   $$
--
--   The supporting exact specification is
--
--   $$
--   M=8^k=n^3,\qquad N=C_8(k),\qquad
--   C_8(0)=1,\quad C_8(k+1)=1+8C_8(k).
--   $$
--
--   Lean proves $7C_8(k)+1=8^{k+1}$ and $8^k\le C_8(k)\le2\cdot8^k$.
--   Consequently $2n^3\le T\le3n^3$ for every permitted size, strengthening the
--   headline's lower bound. The upper witness $C=3$ is uniform; every unnamed
--   clock has zero increment. Initial clock
--   values are arbitrary and do not change the bound on increments.
--
--   ## What the formal result supplies
--
--   `CLRS.Chapter4Publication.MatrixRecursive.correctness_and_running_time` combines
--   the actual returning call, mathematical product, preserved caller storage,
--   fresh output allocation, exact clock increments, and uniform runtime bound.
--   All these conclusions concern the same final heap.
--
--   The source execution summary identifies the actual final heap and counters of eight-way recursion. Its value and allocation theorems establish ordinary matrix multiplication in independently writable result rows. A caller reuses these properties together without reconstructing the recursive execution proof.
--
--   ## Where the specification needs care
--
--   Eight recursive products update overlapping output quadrants by accumulation.
--   The full product claim must therefore account for previous contributions,
--   coordinate offsets, and separation between writable result rows and input
--   rows. A recurrence detached from these updates would establish neither the
--   returned product nor its connection to the charged source execution.
--
--   ## Formalization scope and algorithm source
--
--   The verified entry point creates its own correctly separated output; callers
--   need no separation between input matrices. A direct call to the lower-level
--   `matrix_block` needs its separate writable-output contract. Dimension zero,
--   non-power-of-two dimensions, automatic padding, and rectangular matrices are
--   outside the main result. The code does not validate these size assumptions.
--
--   The exact standalone source is
--   [`examples/matrix_recursive.algo`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/matrix_recursive.algo),
--   with proof
--   [`examples/analysis/matrix_recursive.lean`](https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/analysis/matrix_recursive.lean).
--   The work model excludes row allocation, uncharged source operations, generated
--   transition counts, elapsed time, and integer bit complexity. Alternative
--   proofs must quantify over every valid represented input and establish actual
--   compiled termination; assuming a returning call is insufficient. Compiler
--   provenance is development commit
--   `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41` from
--   `chutongyang98/Lean_formalization`, branch `codex/clrs-chapter-4`, with Lean
--   4.26.0. This is not public v0.1.4. The proofs are handwritten analysis of
--   generated definitions; exact generation alone does not prove the compiler
--   correct.
--   Algo2Lean was created by Lunjia Hu; Chutong Yang is a contributor, and both are
--   software citation authors.
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
--   `CLRS.Chapter4Publication.MatrixRecursive.correctness_and_running_time`, from
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
--   Algo2Lean Chapter 4 development, declaration Chapter4Publication.MatrixRecursive.correctness_and_running_time, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Publication/MatrixContracts.lean#L147-L186

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
namespace CLRS.Chapter4Publication.MatrixRecursive
end CLRS.Chapter4Publication.MatrixRecursive
open CLRS.Chapter4Publication CLRS.Chapter4Publication.MatrixRecursive

theorem CLRS.Chapter4Publication.MatrixRecursive.correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
      ∀ (heap : Heap) (a b : CollectionRef) (av bv : Values) (depth : Nat),
        Stored heap a av → Stored heap b bv →
        ∃ after result,
          MatrixRecursiveLibrary.matrix_recursive.Call heap (a, b, ((2^depth : Nat) : Int)) after result ∧
          Stored after result (product (2^depth) av bv) ∧ Extends heap after ∧
          heap.nextCollection ≤ result ∧ result < after.nextCollection ∧
          FreshRows heap after result (2^depth) ∧
          heap.Increments after (MatrixRecursiveAnalysis.costs depth) ∧
          ((2^depth : Nat)^3) ≤ runtime (heap.cost after) ∧
          runtime (heap.cost after) ≤ C*((2^depth : Nat)^3) := by sorry
