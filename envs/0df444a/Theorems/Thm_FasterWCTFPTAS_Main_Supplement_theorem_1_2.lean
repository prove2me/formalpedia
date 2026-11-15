-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_Supplement_theorem_1_2
-- name    : FasterWCTFPTAS.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:11:13.905889+00:00
-- url     : https://prove2.me/theorems/b710bd12-cd81-4736-96a0-5c7aa4a87b9a
-- title:
--   Theorem 1.2 — conditional FPTAS lower bound
-- statement:
--   Assume CNF-SETH on the published common machine. For every fixed number of machines $m\ge2$ and every $\alpha,\beta>0$, there is no FPTAS for minimizing total weighted completion time on identical parallel machines running in
--
--   $$O\!\left(n^\beta(1/\varepsilon)^{(m-1)/2-\alpha}\right).$$
--
--   The forbidden scheme must output an assignment of cost at most $(1+\varepsilon)\operatorname{OPT}$ for every $n\ge1$, all real $p_j>0,w_j\ge0$ and every $0<\varepsilon\le1$, with one admissible program and constant uniform over all those inputs. Costs are evaluated in the published Smith order and OPT is over all schedules. All-zero weights remain allowed. Every positive $\alpha$ is retained, even when the exponent is nonpositive. This is a companion theorem, not used to prove the goal Theorem 1.1; Corollary A.7 and Lemma B.1 support it.
--
--   Differences from the source:
--   - reading: the source does not name a computational machine → CNF-SETH and the ruled-out algorithms use the published deterministic real RAM; reason: fixes one common machine without transferring a word-RAM assumption to a stronger conclusion
--   - encoding: O(f) algorithm → one finite admissible program and one C > 0, uniform over every input, with actual runtime at most C f; reason: makes the uniform multiplicative constant and program quantifiers explicit
--   - encoding: CNF-SETH for positive exponential improvements and M clauses → CNFSETH uses 0 < δ < 1, canonical finite-set clauses and max(1,M); reason: smaller improvements exclude every positive exponential improvement; canonicalization bounds input length, and padding only treats the empty formula
--   - reading: FPTAS accuracy is stated as ε > 0 → 0 < ε ≤ 1 and n ≥ 1, with the published scheduling input and assignment output; reason: uses the base mission’s accepted FPTAS accuracy and empty-input conventions; an unpadded time monomial tending to zero cannot hold on arbitrarily large accuracies
--   - encoding: an output schedule and optimal scheduling cost → an assignment in Smith order with the published OPT over all schedules; reason: Smith’s rule loses no feasible optimum; the existing base data and conventions are reused unchanged
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, A Faster FPTAS for Weighted Completion Time Scheduling, STOC 2027 submission #1072 (October 2026), p.2 (PDF p.3), Theorem 1.2.

import Definitions.Def_FasterWCTFPTAS_Main_Supplement_SchedulingPrograms

set_option autoImplicit false

namespace FasterWCTFPTAS.Main.Supplement

/-- Theorem 1.2, printed p.2 (PDF 3), restated printed p.29 (PDF 30).
Companion theorem; not used in the proof of the published goal Theorem 1.1. -/
theorem theorem_1_2 :
    CNFSETH → ∀ m : ℕ, 2 ≤ m → ∀ α β : ℝ, 0 < α → 0 < β →
      ¬ FastScheduling m α β := by sorry

end FasterWCTFPTAS.Main.Supplement
