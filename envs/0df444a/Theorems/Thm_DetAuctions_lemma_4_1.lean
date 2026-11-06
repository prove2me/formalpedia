-- Prove2me | Theorems.Thm_DetAuctions_lemma_4_1
-- name    : DetAuctions.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:09.809656+00:00
-- url     : https://prove2.me/theorems/49679ab0-e38f-41cd-9380-3869b9a5a25e
-- title:
--   Lemma 4.1 — tail bounds by $r_j$, $\mathsf{SREV}$ and $\mathsf{BREV}$
-- statement:
--   Let $X_1,\dots,X_m$ be independent nonnegative random variables, $r_j=\mathsf{REV}(X_j)$, $S=\mathsf{SREV}(X)$ and $B=\mathsf{BREV}(X)$, and write $\bar F_j(u)=\mathrm{Prob}[X_j>u]$. Then for every $u>0$:
--   1. $\displaystyle \mathrm{Prob}[X_j>u]\le \frac{r_j}{u}$ for every $j$;
--   2. $\displaystyle \sum_{j=1}^m\bar F_j(u)\le\frac{S}{u}$;
--   3. $\displaystyle \mathrm{Prob}\Big[\sum_{j=1}^m X_j>u\Big]\le\frac{B}{u}$;
--   4. if moreover $u>B$, then $\displaystyle\sum_{j=1}^m\bar F_j(u)\le-\ln(1-B/u)$.
--
--   These elementary bounds on tails and tail sums are used throughout the paper's approximation proofs.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. The first three bounds are in $[0,\infty]$; the fourth is stated only for $u>B$, where it is defined.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: −ln(1 − B/u), "defined only for u > B" → the fourth bound as an implication under BRev < u, with the real logarithm; reason: this is the domain the page gives; there B is finite and 1 − B/u ∈ (0, 1]
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Lemma 4.1, Eq. (22)–(23), pp.15–16 (pdf pp.17–18)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Lemma 4.1 (tail bounds)**: for independent `X₁, …, X_m` with `rⱼ = REV(Xⱼ)`, `S = SREV(X)` and
`B = BREV(X)`, for every `u > 0`:
`Prob[Xⱼ > u] ≤ rⱼ/u`, `Σⱼ F̄ⱼ(u) ≤ S/u` (22), `Prob[Σⱼ Xⱼ > u] ≤ B/u`, and
`Σⱼ F̄ⱼ(u) ≤ −ln(1 − B/u)` (23), the last bound for `u > B`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Lemma 4.1, Eq. (22)–(23), pp.15–16.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
`F̄ⱼ(u) = Prob[Xⱼ > u]` is `tail (ν j) u`. The first three bounds are stated in `ℝ≥0∞` (division by
`u > 0`; a revenue `+∞` gives the trivial bound `+∞`). The last is assumed only when `B < u`
("defined only for u > B"), which makes `B` finite and `1 − B/u ∈ (0, 1]`, so the real
logarithm is the paper's. -/
theorem lemma_4_1 {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ j, IsProbabilityMeasure (ν j)] (u : ℝ) (hu : 0 < u) :
    (∀ j, tail (ν j) u ≤ Rev1 (ν j) / ENNReal.ofReal u) ∧
    ∑ j, tail (ν j) u ≤ SRev (Measure.pi ν) / ENNReal.ofReal u ∧
    Measure.pi ν {x | u < ((∑ j, x j : ℝ≥0) : ℝ)} ≤ BRev (Measure.pi ν) / ENNReal.ofReal u ∧
    (BRev (Measure.pi ν) < ENNReal.ofReal u →
      ∑ j, tail (ν j) u ≤
        ENNReal.ofReal (-Real.log (1 - (BRev (Measure.pi ν)).toReal / u))) := by sorry

end DetAuctions
