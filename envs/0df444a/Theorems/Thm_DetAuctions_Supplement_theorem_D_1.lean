-- Prove2me | Theorems.Thm_DetAuctions_Supplement_theorem_D_1
-- name    : DetAuctions.Supplement.theorem_D_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:43:49.087205+00:00
-- url     : https://prove2.me/theorems/4ffc42fa-1515-4b1a-b902-a82cd9a2aacc
-- title:
--   Theorem D.1 — some product distribution has $\mathsf{REV}>2.19\max\{\mathsf{SREV},\mathsf{BREV}\}$, realized by a deterministic mechanism
-- statement:
--   There exists a product distribution $\boldsymbol F=F_1\times\cdots\times F_m$ of nonnegative item values (for some finite number $m$ of items) such that
--   $$\mathsf{REV}(\boldsymbol F)>2.19\,\max\{\mathsf{SREV}(\boldsymbol F),\mathsf{BREV}(\boldsymbol F)\}.$$
--   Furthermore, this separation can be realized by a truthful deterministic mechanism: on the same $\boldsymbol F$ some incentive compatible, individually rational mechanism whose allocation lies in $\{0,1\}^m$ has expected revenue greater than $2.19\max\{\mathsf{SREV}(\boldsymbol F),\mathsf{BREV}(\boldsymbol F)\}$.
--
--   This is a lower bound complementing the upper bound $2.5$ of Theorem 1.1 for the better of separate selling and grand bundling.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`; "truthful" is its admissibility (allocation in $[0,1]^m$, incentive compatibility, individual rationality, measurable payment) and "deterministic" is the supplement's `IsDeterministic`. The item distributions need not be identical; $2.19=219/100$ exactly, and the strict inequality excludes $\max\{\mathsf{SREV},\mathsf{BREV}\}=\infty$.
--
--   Differences from the source:
--   - encoding: "a (truthful) deterministic mechanism realizes the separation" → an admissible, deterministic mechanism on the same product law whose expected payment exceeds 2.19·max{SREV, BREV}; reason: this is what realizing the separation means; it implies the first sentence since REV is the supremum over admissible mechanisms.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Theorem D.1, p.43 (pdf p.45); deterministic mechanisms per footnote 6, p.7 (pdf p.9)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_Supplement_IsDeterministic

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions.Supplement

/-- **Theorem D.1**: there exists a product distribution `F` such that
`REV(F) > 2.19 max{SREV(F), BREV(F)}`. Furthermore, this separation can be realized by a
(truthful) deterministic mechanism.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Theorem D.1, p.43 (pdf p.45).

**Formalization Note** The model is the published `MultiItemRev.Decomp`; a product distribution
is `Measure.pi ν` for a finite item type `ι` and probability laws `ν j` on `[0, ∞)` (not
necessarily identical). `2.19 = 219/100` exactly, in `ℝ≥0∞`; the strict inequality rules out
`max{SREV, BREV} = ∞`. "Truthful" is the published `IsAdmissible` (feasible, DSIC, IR, measurable
payment) and "deterministic" is `IsDeterministic` (allocation in `{0,1}^m`, footnote 6). Both
sentences are stated for the same instance; the realized revenue is the expected payment
`expRevenue` (an `EReal`) mapped to `ℝ≥0∞`. -/
theorem theorem_D_1 :
    ∃ (ι : Type) (_ : Fintype ι) (ν : ι → Measure ℝ≥0) (_ : ∀ j, IsProbabilityMeasure (ν j)),
      219 / 100 * max (SRev (Measure.pi ν)) (BRev (Measure.pi ν)) < Rev (Measure.pi ν) ∧
      ∃ M : Mechanism ι, IsAdmissible M ∧ IsDeterministic M ∧
        219 / 100 * max (SRev (Measure.pi ν)) (BRev (Measure.pi ν)) <
          (expRevenue (Measure.pi ν) M).toENNReal := by sorry

end DetAuctions.Supplement
