-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_Supplement_corollary_A_7
-- name    : FasterWCTFPTAS.Main.Supplement.corollary_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:09:38.047323+00:00
-- url     : https://prove2.me/theorems/bbdb30ad-2176-4e37-a30d-6564b8aee957
-- title:
--   Corollary A.7 — Grouped Partition lower bound
-- statement:
--   Assume CNF-SETH on the published common machine. For every fixed integer $k\ge2$ and every $\eta,\beta>0$, Grouped $k$-way Partition on $n=ksq$ items of value at most $W$ has no algorithm running in
--
--   $$O\!\left(n^\beta W^{k-1-\eta}\right).$$
--
--   Each group is a set of $ks$ positive integers in $[W(1-1/n^{10}),W]$, with $s,q,W>0$. A solution puts exactly $s$ items of each group in each of $k$ bins and makes the total sum of every bin equal. Uniform program and constant may depend only on $k,\eta,\beta$. This supports Theorem 1.2 through the paper's partition hardness and gap reduction; no cited reduction is added as a hypothesis.
--
--   Differences from the source:
--   - reading: the source does not name a computational machine → CNF-SETH and the ruled-out algorithms use the published deterministic real RAM; reason: fixes one common machine without transferring a word-RAM assumption to a stronger conclusion
--   - encoding: O(f) algorithm → one finite admissible program and one C > 0, uniform over every input, with actual runtime at most C f; reason: makes the uniform multiplicative constant and program quantifiers explicit
--   - encoding: CNF-SETH for positive exponential improvements and M clauses → CNFSETH uses 0 < δ < 1, canonical finite-set clauses and max(1,M); reason: smaller improvements exclude every positive exponential improvement; canonicalization bounds input length, and padding only treats the empty formula
--   - encoding: finite groups, subsets, and one-based indices → zero-based Fin arrays and position selections with explicit fixed input/output layouts; reason: enumerates the same objects; row injectivity is required only for sets and duplicates remain distinct in multisets
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.26 (PDF p.27), Corollary A.7.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_PartitionPrograms

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- Corollary A.7, printed p.26 (PDF 27): support for Theorem 1.2. -/
theorem corollary_A_7 :
    CNFSETH → ∀ k : ℕ, 2 ≤ k → ∀ η β : ℝ, 0 < η → 0 < β →
      ¬ FastGrouped k η β := by sorry

end FasterWCTFPTAS.Main.Supplement
