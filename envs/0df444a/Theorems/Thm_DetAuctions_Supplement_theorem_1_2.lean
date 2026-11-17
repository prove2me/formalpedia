-- Prove2me | Theorems.Thm_DetAuctions_Supplement_theorem_1_2
-- name    : DetAuctions.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:42:34.773546+00:00
-- url     : https://prove2.me/theorems/2d8ec63e-7c11-4c3e-91d9-7b667481db2d
-- title:
--   Theorem 1.2 — $\mathsf{REV}(F^m)\le\min\{2.15\max\{\mathsf S,\mathsf B\},\,2.5\,\mathsf B,\,H_m\mathsf S\}$ for iid items
-- statement:
--   Consider a single additive buyer and $m$ items whose values are independent and identically distributed, each with distribution $F$ on $[0,\infty)$, so that the joint law is $F^m$. With $\mathsf S=\mathsf{SREV}(F^m)$ the revenue of selling the items separately, $\mathsf B=\mathsf{BREV}(F^m)$ the optimal grand-bundling revenue and $H_m=\sum_{i=1}^m1/i$,
--   $$\mathsf{REV}(F^m)\le\min\{2.15\cdot\max\{\mathsf S,\mathsf B\},\;2.5\cdot\mathsf B,\;H_m\cdot\mathsf S\}.$$
--   Here $\mathsf{REV}$ is the optimal revenue over all truthful, possibly randomized mechanisms, and $F$ is an arbitrary distribution on $[0,\infty)$.
--
--   For iid items the better-of-two guarantee improves from $2.5$ to $2.15$, and grand bundling alone is a $2.5$-approximation.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`; revenues are in $[0,\infty]$. The constants are exactly $43/20$ and $5/2$; the minimum is the conjunction of the three inequalities.
--
--   Differences from the source:
--   - generalization: the surrounding text announces the bounds for m ≥ 2 items → every finite number of items, including m = 0 and m = 1; reason: the theorem itself prints no restriction; for m = 1 all three revenues coincide and H_1 = 1, for m = 0 every revenue is 0, so the statement specializes to the source's.
--   - encoding: min of three bounds → conjunction of three inequalities in [0, ∞]; reason: equivalent; revenues may be infinite in the published model.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Theorem 1.2, p.5 (pdf p.7)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions.Supplement

/-- **Theorem 1.2** (Approximation Ratios for IID Items): the optimal revenue of any
single-bidder auction with `m` iid items from distribution `F` is at most
`REV(F^m) ≤ min {2.15 · max {S, B}, 2.5 · B, H_m · S}`, where `S = SREV(F^m)` and
`B = BREV(F^m)`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Theorem 1.2, p.5 (pdf p.7).

**Formalization Note** The model is the published `MultiItemRev.Decomp`. The iid law `F^m` is
`Measure.pi (fun _ : ι => ν)` for one arbitrary probability law `ν` on `[0, ∞)`;
`m = Fintype.card ι`. `2.15 = 43/20` and `2.5 = 5/2` exactly, in `ℝ≥0∞`. The minimum of three
bounds is the conjunction of the three inequalities; `H_m` is Mathlib's `harmonic m : ℚ` cast to
`ℝ≥0∞`. The statement is made for every finite `ι`; the paper's surrounding text announces it
for `m ≥ 2`. -/
theorem theorem_1_2 {ι : Type*} [Fintype ι]
    (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    Rev (Measure.pi (fun _ : ι => ν)) ≤
      43 / 20 * max (SRev (Measure.pi (fun _ : ι => ν))) (BRev (Measure.pi (fun _ : ι => ν))) ∧
    Rev (Measure.pi (fun _ : ι => ν)) ≤ 5 / 2 * BRev (Measure.pi (fun _ : ι => ν)) ∧
    Rev (Measure.pi (fun _ : ι => ν)) ≤
      ENNReal.ofReal ((harmonic (Fintype.card ι) : ℚ) : ℝ) *
        SRev (Measure.pi (fun _ : ι => ν)) := by sorry

end DetAuctions.Supplement
