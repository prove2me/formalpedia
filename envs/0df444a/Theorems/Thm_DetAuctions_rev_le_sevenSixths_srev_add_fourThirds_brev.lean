-- Prove2me | Theorems.Thm_DetAuctions_rev_le_sevenSixths_srev_add_fourThirds_brev
-- name    : DetAuctions.rev_le_sevenSixths_srev_add_fourThirds_brev
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:06.229776+00:00
-- url     : https://prove2.me/theorems/607154c1-0440-4cb7-b640-6497147cd2f2
-- title:
--   Proposition 4.6 — $\mathsf{REV}\le\frac76\mathsf{SREV}+\frac43\mathsf{BREV}\le\frac52\max\{\mathsf{SREV},\mathsf{BREV}\}$
-- statement:
--   A seller offers $m$ items to a single additive buyer whose values $X_1,\dots,X_m$ for the items are independent nonnegative random variables, with arbitrary laws on $[0,\infty)$. Let $\mathsf{REV}(X)$ be the optimal expected revenue over all truthful (DSIC and IR) mechanisms, lotteries included; $\mathsf{SREV}(X)=\sum_j\mathsf{REV}(X_j)$ the optimal revenue from selling the items separately; and $\mathsf{BREV}(X)=\mathsf{REV}(X_1+\dots+X_m)$ the optimal revenue from selling the grand bundle. Then
--   $$\mathsf{REV}(X)\le\frac76\,\mathsf{SREV}(X)+\frac43\,\mathsf{BREV}(X)\le\frac52\,\max\{\mathsf{SREV}(X),\mathsf{BREV}(X)\}.$$
--
--   The better of the two simple deterministic auctions thus earns at least $2/5$ of the optimal revenue for any number of independent items, improving the earlier constant $5.2$ of Ma and Simchi-Levi (and the constant $6$ of Babaioff, Immorlica, Lucier and Weinberg).
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. No boundedness or moment condition is assumed and any finite number of items is allowed; with values in $[0,\infty]$ no finiteness hypothesis is needed. Both inequalities are stated.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Proposition 4.6, Eq. (30), p.19 (pdf p.21)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Proposition 4.6**: for any independent random variables `X₁, X₂, …, X_m`,
`REV(X) ≤ (7/6)·SREV(X) + (4/3)·BREV(X) ≤ (5/2)·max{SREV(X), BREV(X)}` (30).

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Proposition 4.6, Eq. (30), p.19.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The item laws are arbitrary probability laws on `[0, ∞)`: unbounded, atomic or continuous, with
no moment condition, and any finite number of items. Revenues are in `ℝ≥0∞` (`SREV = ∞` makes
both sides `∞`), so no finiteness is assumed. The mechanism class is the whole class of
DSIC, IR mechanisms with lotteries (no restriction to deterministic or NPT mechanisms). Both
inequalities of (30) are stated. -/
theorem rev_le_sevenSixths_srev_add_fourThirds_brev {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)] :
    Rev (Measure.pi ν) ≤ 7 / 6 * SRev (Measure.pi ν) + 4 / 3 * BRev (Measure.pi ν) ∧
    7 / 6 * SRev (Measure.pi ν) + 4 / 3 * BRev (Measure.pi ν) ≤
      5 / 2 * max (SRev (Measure.pi ν)) (BRev (Measure.pi ν)) := by sorry

end DetAuctions
