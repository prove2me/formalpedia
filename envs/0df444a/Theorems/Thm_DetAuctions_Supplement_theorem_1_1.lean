-- Prove2me | Theorems.Thm_DetAuctions_Supplement_theorem_1_1
-- name    : DetAuctions.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:42:11.623214+00:00
-- url     : https://prove2.me/theorems/9caa5545-c064-451a-b0f7-d17e14a60391
-- title:
--   Theorem 1.1 — $\mathsf{REV}\le\min\{2.5\max\{\mathsf S,\mathsf B\},\,H_m\mathsf S,\,(m+1)\mathsf B\}$ for independent items
-- statement:
--   Consider a single additive buyer and $m$ items whose values $X_1,\dots,X_m\ge0$ are independent, $X_j\sim F_j$, and write $\boldsymbol F=F_1\times\cdots\times F_m$. Let $\mathsf{REV}(\boldsymbol F)$ be the optimal revenue over all truthful (incentive compatible and individually rational) mechanisms, possibly randomized, $\mathsf S=\mathsf{SREV}(\boldsymbol F)=\sum_j\mathsf{REV}(F_j)$ the revenue of selling the items separately, and $\mathsf B=\mathsf{BREV}(\boldsymbol F)$ the optimal revenue of selling the grand bundle. With $H_m=\sum_{i=1}^m 1/i$ the $m$-th harmonic number,
--   $$\mathsf{REV}(\boldsymbol F)\le\min\{2.5\cdot\max\{\mathsf S,\mathsf B\},\;H_m\cdot\mathsf S,\;(m+1)\cdot\mathsf B\}.$$
--   The distributions $F_j$ on $[0,\infty)$ are arbitrary: unbounded, atomic or continuous, with no moment condition.
--
--   The first bound is a constant-factor guarantee for the better of the two simple mechanisms; the second and third show that separate selling alone and grand bundling alone are within factors $H_m$ and $m+1$ of optimal.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`; revenues are in $[0,\infty]$, so no finiteness is assumed. The minimum is stated as the conjunction of the three inequalities, $H_m$ is Mathlib's `harmonic`, and $m$ is the number of items.
--
--   Differences from the source:
--   - generalization: the surrounding text announces the bounds for m ≥ 2 items → every finite number of items, including m = 0 and m = 1; reason: the theorem itself prints no restriction; for m = 1 all three revenues coincide and H_1 = 1, for m = 0 every revenue is 0, so the statement specializes to the source's.
--   - encoding: min of three bounds → conjunction of three inequalities in [0, ∞]; reason: equivalent; revenues may be infinite in the published model.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Theorem 1.1, p.5 (pdf p.7)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions.Supplement

/-- **Theorem 1.1** (Approximation Ratios for Independent Items): the optimal revenue of any
single-bidder auction with `m` items independently drawn from `F₁, …, F_m` is at most
`REV(F) ≤ min {2.5 · max {S, B}, H_m · S, (m + 1) · B}`, where `F = F₁ × ⋯ × F_m`,
`S = SREV(F)` and `B = BREV(F)`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Theorem 1.1, p.5 (pdf p.7).

**Formalization Note** The model is the published `MultiItemRev.Decomp` (values in `ι → ℝ≥0`,
DSIC and IR mechanisms with lotteries and measurable payment; `Rev`, `SRev`, `BRev` in `ℝ≥0∞`).
Independent items are `Measure.pi ν` for arbitrary probability laws `ν j` on `[0, ∞)` (unbounded,
atomic or continuous, no moment condition); `m = Fintype.card ι`. The minimum of three bounds is
stated as the conjunction of the three inequalities. `H_m = Σ_{i=1}^m 1/i` is Mathlib's
`harmonic m : ℚ`, cast to `ℝ≥0∞`. Revenues may be `∞`, so no finiteness is assumed. The
statement is made for every finite `ι`; the paper's surrounding text announces it for `m ≥ 2`. -/
theorem theorem_1_1 {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)] :
    Rev (Measure.pi ν) ≤ 5 / 2 * max (SRev (Measure.pi ν)) (BRev (Measure.pi ν)) ∧
    Rev (Measure.pi ν) ≤
      ENNReal.ofReal ((harmonic (Fintype.card ι) : ℚ) : ℝ) * SRev (Measure.pi ν) ∧
    Rev (Measure.pi ν) ≤ ((Fintype.card ι : ℝ≥0∞) + 1) * BRev (Measure.pi ν) := by sorry

end DetAuctions.Supplement
