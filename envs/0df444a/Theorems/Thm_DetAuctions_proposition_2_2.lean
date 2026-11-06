-- Prove2me | Theorems.Thm_DetAuctions_proposition_2_2
-- name    : DetAuctions.proposition_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:37.357894+00:00
-- url     : https://prove2.me/theorems/e4bb4b2f-553e-41e6-8402-007fd30ba5d3
-- title:
--   Proposition 2.2 — discrete vs general distributions on $[0,1]^m$
-- statement:
--   Let $X$ be a random vector in the unit hypercube $[0,1]^m$ (no independence is assumed), and $X^{(K)}=\lfloor KX\rfloor/K$ its downward discretization in the grid $I_K^m$, for a positive integer $K$. Then
--   $$0\le R(X)-R(X^{(K)})\le\frac mK\qquad\text{for every }R\in\{\mathsf{SREV},\mathsf{BREV},\max\{\mathsf{SREV},\mathsf{BREV}\}\},$$
--   and
--   $$\big|\mathsf{REV}(X)-\mathsf{REV}(X^{(K)})\big|\le\frac{2m}{\sqrt K}-\frac mK .$$
--
--   It transfers every revenue bound proved on the grid to arbitrary distributions on $[0,1]^m$ by letting $K\to\infty$.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. Each difference bound is stated in $[0,\infty]$ as two inequalities; the trailing $=O(m/\sqrt K)$ of (7) is implied and omitted.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: X over the unit hypercube I^m; real differences 0 ≤ R(X) − R(X^(K)) ≤ m/K and |REV(X) − REV(X^(K))| ≤ 2m/√K − m/K → μ {x | ∀ j, x j ≤ 1}ᶜ = 0; each bound as a pair of inequalities in ℝ≥0∞; reason: all revenues are at most m here, so the pairs are equivalent to the real statements
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Proposition 2.2 (Discrete vs General Distributions), Eq. (6)–(7), p.10 (pdf p.12)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_discretize

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Proposition 2.2 (Discrete vs General Distributions)**: for a random variable `X` over the
unit hypercube `I^m` and its downward discretization `X^(K)` in the unit `K`-grid, for every
positive integer `K`,
`0 ≤ R(X) − R(X^(K)) ≤ m/K` for `R ∈ {SREV, BREV, max{SREV, BREV}}` (6), and
`|REV(X) − REV(X^(K))| ≤ 2m/√K − m/K` (7).

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Proposition 2.2, Eq. (6)–(7), p.10.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
No independence is assumed (the proposition has none). `X ∈ I^m` almost surely is
`μ {x | ∀ j, x j ≤ 1}ᶜ = 0`; `m = Fintype.card ι`. The differences are stated in `ℝ≥0∞` as two
inequalities each (all revenues are at most `m` here). `2m/√K − m/K ≥ 0` for `K ≥ 1`, so
`ENNReal.ofReal` does not truncate it. The trailing `= O(m/√K)` of (7) is implied and omitted. -/
theorem proposition_2_2 {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ≥0))
    [IsProbabilityMeasure μ] (hcube : μ {x | ∀ j, x j ≤ 1}ᶜ = 0) (K : ℕ) (hK : 1 ≤ K) :
    (SRev (discretize K μ) ≤ SRev μ ∧
      SRev μ ≤ SRev (discretize K μ) + (Fintype.card ι : ℝ≥0∞) / (K : ℝ≥0∞)) ∧
    (BRev (discretize K μ) ≤ BRev μ ∧
      BRev μ ≤ BRev (discretize K μ) + (Fintype.card ι : ℝ≥0∞) / (K : ℝ≥0∞)) ∧
    (max (SRev (discretize K μ)) (BRev (discretize K μ)) ≤ max (SRev μ) (BRev μ) ∧
      max (SRev μ) (BRev μ) ≤ max (SRev (discretize K μ)) (BRev (discretize K μ)) +
        (Fintype.card ι : ℝ≥0∞) / (K : ℝ≥0∞)) ∧
    (Rev μ ≤ Rev (discretize K μ) +
        ENNReal.ofReal (2 * (Fintype.card ι : ℝ) / Real.sqrt K - (Fintype.card ι : ℝ) / K) ∧
      Rev (discretize K μ) ≤ Rev μ +
        ENNReal.ofReal (2 * (Fintype.card ι : ℝ) / Real.sqrt K - (Fintype.card ι : ℝ) / K)) := by sorry

end DetAuctions
