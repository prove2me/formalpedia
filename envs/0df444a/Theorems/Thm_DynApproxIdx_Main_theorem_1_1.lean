-- Prove2me | Theorems.Thm_DynApproxIdx_Main_theorem_1_1
-- name    : DynApproxIdx.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:53:24.496193+00:00
-- url     : https://prove2.me/theorems/d73442f8-971f-4ed7-9736-fe40e304b3fc
-- title:
--   Theorem 1.1 — a dynamic k-mismatch and k-edit text index with Õ(c^k log^k n/k!) update time and Õ(m + c^k log^k n/k!) query time, w.h.p., always correct
-- statement:
--   Let $k\ge1$ be an integer. A text $T$ over the alphabet $\mathbb N$, initially empty, undergoes character insertions and deletions, and queries with a nonempty pattern $P$ of length $m$ asking for one, or all, $k$-mismatch occurrences, or one, or all, $k$-edit occurrences of $P$ in $T$. Let $n=\max(|T|,2^k)$ and $F=c^k\log^k n/k!$.
--
--   **Theorem 1.1.** *There is a constant $c>1$ such that a text $T$ can be maintained in $\tilde O(F)$ time per update and $\tilde O(n\cdot F)$ space, so that one $k$-mismatch or $k$-edit occurrence of $P$ is returned in $\tilde O(m+F)$ time, all $k$-mismatch occurrences are reported in $\tilde O(m+F+\mathrm{occ})$ time, and all $k$-edit occurrences in $\tilde O(m+F+3^k\cdot\mathrm{occ})$ time. The time and space bounds hold w.h.p. in $n$, and queries are always answered correctly.*
--
--   Precisely: there are $c>1$ and an exponent $e$ such that for every $a>0$ there are one program $P$ of the word RAM, a constant $C$ and a width constant $c_w$ such that, for every $k\ge1$, every valid operation sequence $\sigma$ fixed before the coin tape, and every word size $w\ge c_w\lceil\log_2(N+\sigma_{\max}+3)\rceil$:
--   - for every operation $j$ (operation $0$ reads $k$),
--   $$\Pr_\omega\bigl[\text{operation } j \text{ exceeds its time bound, or more than } C\,n_jF_jL_j^e \text{ cells are nonzero at some step of it}\bigr]\le n_j^{-a},$$
--   with $n_j=\max(|T|,2^k)$ for the text $T$ it meets, $L_j=\log_2 n_j$, $F_j=c^kL_j^k/k!$, and time bound $C F_jL_j^e$ (initialization, update), $C(m+F_j)L_j^e$ (one occurrence), $C(m+F_j+\mathrm{occ})L_j^e$ (all $k$-mismatch), $C(m+F_j+3^k\mathrm{occ})L_j^e$ (all $k$-edit);
--   - on every coin tape, every query that completes writes a correct answer.
--
--   This is the paper's main result: the first dynamic approximate text index whose update time is $n^{o(1)}$ and whose query time is $\tilde O(m+\mathrm{occ})+n^{o(1)}$ for $k=o(\log n)$.
--
--   Differences from the source:
--
--   - reading: Õ(·) hides factors polylogarithmic in n (polynomial in k included, since k ≤ log n) → Õ(g) = C·g·(log₂ n_j)^e with c and e fixed first (before a) and C chosen with the program; reason: c is printed as an absolute constant; e is the fixed polylog exponent of the construction; C may depend on the failure exponent a, as the constant of a w.h.p. bound does
--   - reading: the time and space complexities hold w.h.p. in n (footnote 2: success probability 1 − n^{−a} for an arbitrarily large constant a) → for every a > 0 a program (with C, c_w) such that, for every operation j, the coin tapes on which operation j exceeds its time bound or its space bound have (outer) measure ≤ n_j^{−a}; reason: per operation, worst case (Appendix A deamortizes); the program may depend on a, as 'arbitrarily large constant a' allows
--   - reading: n = max(|T|, 2^k), space Õ(n·F) → n_j = max(|T|, 2^k) for the text T operation j meets (n_0 = 2^k); space = number of nonzero memory cells, bounded at every step of every operation by C·n_j·F_j·L_j^e; reason: a bound at every step is the space in use; the cumulative set of written cells is not space when the text shrinks
--   - reading: k is specified at construction time; Appendix A: the initial structure is built within the time bound of a single update with n = 2^k → one program for every k ≥ 1, reading k as its first input word (operation 0 on the empty text), with the update bound at n_0 = 2^k; reason: the structure is built for a given k; one program serving every k is the uniform reading of 'given integer k > 0'
--   - reading: one k-mismatch or k-edit occurrence; all k-mismatch (resp. k-edit) occurrences → one structure answering all four query kinds; reason: the stronger reading; a structure per distance is two instances of it
--   - reading: queries are always answered correctly → on every coin tape, every query operation that completes writes a correct answer; reason: correctness is not part of the w.h.p. event
--   - encoding: the machine model (unstated): word RAM with random bits → the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write-only output), online protocol of Run; word size w ≥ c_w ⌈log₂(N + σ_max + 3)⌉ for every such w, N = max(2^k, all text lengths), σ_max the largest word of σ; reason: the paper's structures (Theorem 3.1, AVL trees, hashing) are word-RAM structures with Θ(log N)-bit words
--   - encoding: the sequence of updates and queries is fixed in advance (Appendix B, oblivious adversary) → ∀ σ quantified before the coin tape ω; operations delivered one at a time to completed states; reason: the blocking read prevents look-ahead
--   - encoding: integer alphabet; trivial queries with empty P or T are omitted (§3) → characters are naturals with no bound; a valid query has P ≠ [] and T ≠ []; insert at i ≤ |T|, delete at i < |T|; reason: the paper states no alphabet bound and omits exactly the trivial queries
--   - encoding: return one occurrence (if it exists); report all occurrences → operation words 0,i,x / 1,i / 2+code,m,P; a one-occurrence query writes nothing iff there is no occurrence, else one occurrence position; a reporting query writes each occurrence position exactly once, in any order; reason: positions are the starting positions of OccH and Occ; reporting without duplicates is the paper's (§9 filters duplicates)
-- source:
--   Charalampopoulos, Ellert, Radoszewski, Dynamic Approximate Text Indexing, STOC 2027 submission (manuscript sha256 7f902057…), p. 2 (PDF 4), Theorem 1.1, with footnote 2 (p. 2), the Õ convention (abstract footnote 1; §2, p. 5, PDF 7), §3 (p. 13, PDF 15) and Appendices A–B (pp. 56–58, PDF 58–60)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_PMEdits_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Strings
import Definitions.Def_DynApproxIdx_Main_Run
import Definitions.Def_DynApproxIdx_Main_Index

namespace DynApproxIdx.Main

/-- **Theorem 1.1** (Charalampopoulos, Ellert, Radoszewski, *Dynamic Approximate Text Indexing*,
STOC 2027 submission, p. 2 (PDF 4)), with footnote 2 (w.h.p.), the `Õ` convention of p. 5 (PDF 7),
§3 (p. 13) and Appendices A–B.

There are a constant `c > 1` and an exponent `e` such that for every failure exponent `a > 0`
there are one program `P` of the word RAM, a constant `C` and a width constant `c_w` with the
following property. For every `k ≥ 1`, every valid sequence `σ` of insertions, deletions and
queries (one / all `k`-mismatch, one / all `k`-edit occurrences) on an initially empty text, fixed
before the coin tape, and every word size `w ≥ c_w ⌈log₂(N + σ_max + 3)⌉`:
* for every operation `j` (operation `0` reads `k`), the coin tapes on which it exceeds its time
  bound (`C·F·L^e` for the initialization and each update, `C·(m + F)·L^e` for a one-occurrence
  query, `C·(m + F + occ)·L^e` resp. `C·(m + F + 3^k·occ)·L^e` for reporting all `k`-mismatch
  resp. `k`-edit occurrences), or on which more than `C·n·F·L^e` memory cells are nonzero at some
  step of it, have measure at most `n^{−a}`, where `n = max(|T|, 2^k)` for the text `T` it meets,
  `L = log₂ n` and `F = c^k L^k / k!`;
* on every coin tape, every query that completes writes a correct answer. -/
theorem theorem_1_1 :
    ∃ c : ℝ, 1 < c ∧ ∃ e : ℕ, ∀ a : ℝ, 0 < a →
      ∃ (P : DynBrooks.Program) (C : ℝ) (cw : ℕ),
        ∀ k : ℕ, 1 ≤ k → ∀ σ : List Op, ValidSeq σ → ∀ w : ℕ, cw * widthReq k σ ≤ w →
          (∀ j : ℕ, j ≤ σ.length →
            DynBrooks.coinMeasure w {ω | ¬ OpWithin c e C P ω k σ j}
              ≤ ENNReal.ofReal ((nAt k σ j : ℝ) ^ (-a))) ∧
          ∀ ω : ℕ → BitVec w, QueriesCorrect P ω k σ := by sorry

end DynApproxIdx.Main
