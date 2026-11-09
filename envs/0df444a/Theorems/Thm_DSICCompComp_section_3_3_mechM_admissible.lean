-- Prove2me | Theorems.Thm_DSICCompComp_section_3_3_mechM_admissible
-- name    : DSICCompComp.section_3_3_mechM_admissible
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T13:33:20.764809+00:00
-- url     : https://prove2.me/theorems/fb30d974-c459-4a68-b25d-8e2f3fa60abe
-- title:
--   §3.3 — the mechanism $M$ is DSIC/IR ($M \in \mathcal D$)
-- statement:
--   Let $\varepsilon, t, T > 0$. The mechanism $M$, which sells the first $\ell$ items using the affine maximizer with $r$ reserve bidders and Clarke pivot payments and the remaining $m - \ell$ items separately using the second-price auction with reserve $a$, is dominant-strategy incentive compatible and individually rational: for every bidder $i$, every value profile $v$ and every misreport $v_i'$,
--   $$
--   \sum_j x_{ij}(v)\,v_{ij} - p_i(v) \;\ge\; \sum_j x_{ij}(v_i', v_{-i})\,v_{ij} - p_i(v_i', v_{-i}), \qquad \sum_j x_{ij}(v)\,v_{ij} - p_i(v) \ge 0 .
--   $$
--   Moreover $M$ is feasible (each item goes to at most one bidder) and its payments are measurable functions of the profile, so $M$ belongs to the class over which $\mathrm{Rev}^{\mathcal D}_n$ is the supremum.
--
--   Together with the revenue bound of §B.4 this shows that the optimal DSIC/IR revenue is at least the revenue of $M$.
--
--   Differences from the source:
--   - generalization: ℓ ∈ [m], r ≤ n, a ≥ 1 (standing assumptions of §3.2–3.3) → all ℓ, r ∈ ℕ and every real a (ε, t, T > 0 kept); reason: the DSIC/IR argument uses none of them; the statement specializes to the paper's range
--   - generalization: M ∈ 𝒟: M is DSIC/IR → IsAdmissibleDS: feasible, DSIC and IR at every profile in ℝ≥0^{n×m}, and measurable payments; reason: the published class requires feasibility and measurability as well; claiming them is stronger
--   - reading: the remaining items are sold "separately using Myerson's optimal auction" → a second-price auction with reserve a on each item j ≥ ℓ, ties to the lowest index; reason: this is Myerson's auction for the regular D of §3.2 (virtual value 0 below a, a − 1 above)
--   - reading: the affine maximizer chooses "a (deterministic) allocation" maximizing the objective → the first maximizer in a fixed enumeration of the allocations; reason: the source leaves ties open; this is one fixed deterministic rule with measurable payments
--   - encoding: items [ℓ], reserve bidders [r], 1-based → items j < ℓ, reserve bidders i < r, 0-based (Fin m, Fin n); reason: relabelling only
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), §3.3, p.12 (pdf p.13), with footnotes 9 and 10

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model
import Definitions.Def_DSICCompComp_mechM

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DSICCompComp

/-- §3.3, `M ∈ 𝒟` (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*,
STOC 2027 submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…, §3.3, p.12 (pdf p.13), with footnotes 9 and 10): the mechanism `M`,
which sells the first `ℓ` items using the affine maximizer with Clarke pivot payments and the
remaining `m − ℓ` items separately using a second-price auction with reserve `a`, is DSIC/IR:
it is feasible, dominant-strategy incentive compatible and individually rational at every value
profile, and its payments are measurable.

**Formalization Note** Stated for all `n, m, ℓ, r` and every real `a`, with `ε, t, T > 0` (the
paper's `ℓ ∈ [m]`, `r ≤ n`, `a ≥ 1` are not needed). -/
theorem section_3_3_mechM_admissible (n m ℓ r : ℕ) (a ε t T : ℝ) (hε : 0 < ε) (ht : 0 < t)
    (hT : 0 < T) :
    MultiItemRev.MultiBuyer.IsAdmissibleDS (mechM n m ℓ r a ε t T) := by sorry

end DSICCompComp
