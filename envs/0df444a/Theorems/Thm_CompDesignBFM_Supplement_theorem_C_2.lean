-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_C_2
-- name    : CompDesignBFM.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:08:40.086824+00:00
-- url     : https://prove2.me/theorems/d16cd45b-d6eb-4cad-8d04-fe59b0a2a5b0
-- title:
--   Theorem C.2 — Mechanism C.1 is truthful, IR and budget feasible, and selects a cost-feasible set
-- statement:
--   Let $B>0$, $\beta>0$, $v$ normalized and $\beta$-self-bounding, and fix a total order on $2^N$ with $\emptyset$ first. Mechanism C.1, which selects $S^{(\beta)}(b)$ and pays each selected $i$ the amount $\frac B\beta\bigl(1-\Phi^{(\beta)}_{i,\mathrm{out}}(b_{-i})/\Phi^{(\beta)}_{i,\mathrm{in}}(b_{-i})\bigr)$, is
--
--   1. truthful (in dominant strategies, over all nonnegative costs and bids),
--   2. individually rational,
--   3. pays nonnegative amounts to selected agents only, and is budget feasible, $\sum_{i\in S^{(\beta)}(b)}p_i(b)\le B$;
--
--   and under truthful bidding its selected set is cost feasible: $\sum_{i\in S^{(\beta)}(c)}c_i\le B$ for every $c\ge0$.
--
--   This turns the scaled compensation rule into a direct budget-feasible mechanism for $\beta$-self-bounding valuations.
--
--   Differences from the source:
--   - reading: β-self-bounding with β unrestricted → 0 < β; reason: Algorithm C.1 and Φ^{(β)} divide by β; the appendix treats β ≥ 1 classes and never β ≤ 0
--   - encoding: S^{(β)}(c), the maximizer of Φ^{(β)}_c with ties broken by a fixed total order with ∅ first → Amc v (B/β) r c with IsPriority r; reason: pot v (B/β) c = Φ^{(β)}_c because c_i/(B/β) = βc_i/B
--   - encoding: truthful, individually rational, and budget feasible → IsGood B, which also includes nonnegative payments and zero payments to unselected agents; reason: the model of p.1 (the mechanism pays p_i(b) ≥ 0 to each agent i ∈ S), which Mechanism C.1 satisfies by construction
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem C.2, p.47 (PDF 49); Mechanism C.1, p.46 (PDF 48)

import Mathlib
import Definitions.Def_CompDesignBFM_IsPriority
import Definitions.Def_CompDesignBFM_IsGood
import Definitions.Def_CompDesignBFM_Supplement_IsBetaSelfBounding
import Definitions.Def_CompDesignBFM_Supplement_scaledMech

namespace CompDesignBFM

namespace Supplement

/-- Theorem C.2 (direct mechanism), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.47, PDF 49. For every normalized `β`-self-bounding valuation,
Mechanism C.1 is truthful, individually rational, and budget feasible. Under truthful bidding, its
selected set is cost feasible.
**Formalization Note.** `IsGood B` is the base mission's conjunction of dominant-strategy truthfulness,
individual rationality, nonnegative payments to selected agents only (the model of p.1), and budget
feasibility, all over nonnegative bids. "Cost feasible" is `∑_(i ∈ S^(β)(c)) cᵢ ≤ B` at every nonnegative
cost vector `c` reported truthfully. -/
theorem theorem_C_2 {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (hB : 0 < B) (hβ : 0 < β)
    (hv0 : v ∅ = 0) (hv : IsBetaSelfBounding β v) (r : Finset (Fin n) → ℕ) (hr : IsPriority r) :
    IsGood B (scaledMech v B β r) ∧
      ∀ c : Fin n → ℝ, (∀ i, 0 ≤ c i) → ∑ i ∈ (scaledMech v B β r).alloc c, c i ≤ B := by sorry

end Supplement

end CompDesignBFM
