-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_Supplement_theorem_A_3
-- name    : FasterWCTFPTAS.Main.Supplement.theorem_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:12:09.122204+00:00
-- url     : https://prove2.me/theorems/234beb6e-a73d-4f71-86ec-05f79e7b9c61
-- title:
--   Theorem A.3 — multiset weak partition lower bound
-- statement:
--   Assume CNF-SETH on the published common machine. For every fixed $k\ge2$ and every $\eta,\beta>0$, Multiset Weak Grouped $k$-way Partition with targets cannot be solved in
--
--   $$O\!\left(n^\beta W^{k-1-\eta}\right).$$
--
--   The input has natural $s,q,W$, $q$ multisets of size $ks$, $n=ksq$ items and $k-1$ natural targets. Yes requires disjoint selections of exactly $s$ occurrences from every group for every bin and the specified target sums. No forbids the full relaxed witness: every bin's prefix count is at most $is$, the global selected count is at least $(k-1)qs$, and every target sum is met. Runtime and decision correctness are required only on Yes or No, without classifying inputs between the promise sets. One program and one multiplicative constant, depending only on $k,\eta,\beta$, must work for all promised inputs. The natural zero cases use the division-free interval condition and bound $C\max(1,n)^\beta\max(1,W)^{k-1-\eta}$; positive cases have exactly the source bound. This is a companion theorem; its partition hardness is also available when proving Corollary A.7. No average-free-set theorem or cited reduction is assumed.
--
--   Differences from the source:
--   - reading: the source does not name a computational machine → CNF-SETH and the ruled-out algorithms use the published deterministic real RAM; reason: fixes one common machine without transferring a word-RAM assumption to a stronger conclusion
--   - encoding: O(f) algorithm → one finite admissible program and one C > 0, uniform over every input, with actual runtime at most C f; reason: makes the uniform multiplicative constant and program quantifiers explicit
--   - encoding: CNF-SETH for positive exponential improvements and M clauses → CNFSETH uses 0 < δ < 1, canonical finite-set clauses and max(1,M); reason: smaller improvements exclude every positive exponential improvement; canonicalization bounds input length, and padding only treats the empty formula
--   - encoding: finite groups, subsets, and one-based indices → zero-based Fin arrays and position selections with explicit fixed input/output layouts; reason: enumerates the same objects; row injectivity is required only for sets and duplicates remain distinct in multisets
--   - reading: natural s,q,W including zero, with the interval W(1-1/n^10) and time n^β W^{k-1-η} → a ≤ W and n^10(W-a) ≤ W, and max(1,n)^β max(1,W)^{k-1-η} for the zero cases; reason: retains every natural input and makes undefined zero boundaries explicit; equals the printed interval and monomial on every positive instance
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.20 (PDF p.21), Theorem A.3.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_PartitionPrograms

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- Theorem A.3, printed p.20 (PDF 21). Companion theorem; not used in the proof of
the published goal Theorem 1.1. Full multiset promise and every positive exponent saving. -/
theorem theorem_A_3 :
    CNFSETH → ∀ k : ℕ, 2 ≤ k → ∀ η β : ℝ, 0 < η → 0 < β →
      ¬ FastWeak k η β := by sorry

end FasterWCTFPTAS.Main.Supplement
