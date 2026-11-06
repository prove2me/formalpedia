-- Prove2me | Theorems.Thm_DetAuctions_claim_4_7
-- name    : DetAuctions.claim_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:13.282249+00:00
-- url     : https://prove2.me/theorems/1bf618c9-0fbb-4008-81b7-1c5a2d6400a9
-- title:
--   Claim 4.7 — Jensen weights with $\sum_j\pi_j\int_{c_j}^\infty\phi(\bar F_j/\pi_j)\le\frac16\mathsf{SREV}+\frac43\mathsf{BREV}$
-- statement:
--   Let $X_1,\dots,X_m$ ($m\ge1$) be independent nonnegative random variables and caps $c_j$ such that $\mathbb E[X_j\wedge c_j]=r_j=\mathsf{REV}(X_j)$. Then there exist Jensen weights $\pi_j>0$, $\sum_j\pi_j=1$, such that
--   $$\sum_{j=1}^m\pi_j\int_{c_j}^\infty\phi\Big(\frac{\bar F_j(u)}{\pi_j}\Big)du\le\frac16\,\mathsf{SREV}(X)+\frac43\,\mathsf{BREV}(X).$$
--
--   Combined with Lemma 4.4 and (31) this gives $\mathsf{REV}\le\frac76\mathsf{SREV}+\frac43\mathsf{BREV}$.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. The weights are written $w_j$; at least one item is assumed.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: caps c_j with E[X_j ∧ c_j] = r_j → c j : ℝ≥0 with ∫⁻ min x (c j) ∂(ν j) = Rev1 (ν j) in ℝ≥0∞; reason: the same condition; caps are nonnegative as values are
--   - encoding: ∫ over (0, ∞) (or (c_j, ∞)) of a nonnegative integrand → lower integral of ENNReal.ofReal of the integrand over Set.Ioi, in ℝ≥0∞; reason: the integrands are nonnegative, so ofReal loses nothing and the value +∞ is kept
--   - encoding: m items, Jensen weights π_j > 0 with Σ π_j = 1 → [Nonempty ι]; reason: with no items such weights do not exist; the paper always has m ≥ 1
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Claim 4.7, p.19 (pdf p.21)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail
import Definitions.Def_DetAuctions_phi

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Claim 4.7**: for independent items and caps `cⱼ` with `E[Xⱼ ∧ cⱼ] = rⱼ`, there exist Jensen
weights `πⱼ` (`πⱼ > 0`, `Σⱼ πⱼ = 1`, as in (31)) such that
`Σⱼ πⱼ ∫_{cⱼ}^∞ φ(F̄ⱼ(u)/πⱼ) du ≤ (1/6)·SREV + (4/3)·BREV`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Claim 4.7, p.19.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The weights are `w j`. At least one item is assumed (`Nonempty ι`): with no items, weights
summing to `1` do not exist; the paper always has `m ≥ 1`. The left side is a sum of lower
integrals in `ℝ≥0∞`, as in `eq_31`; the constants are `ℝ≥0∞` numerals. -/
theorem claim_4_7 {ι : Type*} [Fintype ι] [Nonempty ι] (ν : ι → Measure ℝ≥0)
    [∀ j, IsProbabilityMeasure (ν j)] (c : ι → ℝ≥0)
    (hc : ∀ j, ∫⁻ x, ((min x (c j) : ℝ≥0) : ℝ≥0∞) ∂(ν j) = Rev1 (ν j)) :
    ∃ w : ι → ℝ, (∀ j, 0 < w j) ∧ ∑ j, w j = 1 ∧
      ∑ j, ENNReal.ofReal (w j) *
          ∫⁻ u in Set.Ioi (c j : ℝ), ENNReal.ofReal (phi ((tail (ν j) u).toReal / w j)) ≤
        1 / 6 * SRev (Measure.pi ν) + 4 / 3 * BRev (Measure.pi ν) := by sorry

end DetAuctions
