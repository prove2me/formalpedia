-- Prove2me | Theorems.Thm_DetAuctions_lemma_4_5
-- name    : DetAuctions.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:11.524071+00:00
-- url     : https://prove2.me/theorems/19c4c0a3-a952-4e51-86b4-238eacc8aa72
-- title:
--   Lemma 4.5 — exponentially weighted tail integrals bounded by $\mathsf{BREV}$
-- statement:
--   Let $X_1,\dots,X_m$ be independent nonnegative random variables and caps $c_j$ chosen such that $\mathbb E[X_j\wedge c_j]=r_j=\mathsf{REV}(X_j)$ for every $j$, and let $B=\mathsf{BREV}(X)$. Then for every $\lambda>0$,
--   $$\sum_{j=1}^m\int_{c_j}^\infty e^{-\lambda u}\bar F_j(u)\,du\le-\frac1\lambda\ln\Big(\int_1^\infty e^{-\lambda Bx}\frac1{x^2}\,dx\Big)-\sum_{j=1}^m r_j\,\frac{1-e^{-\lambda c_j}}{\lambda c_j}.$$
--
--   The bound is free of the tails: it brings in $\mathsf{BREV}$ and subtracts a weighted average of the single-item revenues, and is used to control the integrals in Claim 4.7.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. The statement is real-valued; each integral is finite. $B<\infty$ is assumed (for $B=\infty$ the printed right side is $+\infty$). For $c_j=0$ the fraction $0/0$ is read as $0$; then $r_j=0$.
--
--   Differences from the source:
--   - reading: E[p(X)] over truthful mechanisms (a, p) → payment p measurable (MultiItemRev.Decomp.IsAdmissible); reason: the expectation E[p(X)] presupposes a measurable payment
--   - encoding: REV_V(X) over a value space V ⊆ ℝ₊^m → V = ℝ₊^m (mechanisms on all of ι → ℝ≥0); reason: REV_V(X) = REV_supp(X)(X) for all supp(X) ⊆ V ⊆ ℝ₊^m (p.8)
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: caps c_j with E[X_j ∧ c_j] = r_j → c j : ℝ≥0 with ∫⁻ min x (c j) ∂(ν j) = Rev1 (ν j) in ℝ≥0∞; reason: the same condition; caps are nonnegative as values are
--   - encoding: B = BREV(X) arbitrary → hypothesis BRev ≠ ⊤; reason: for B = ∞ the printed right side is +∞ (ln 0), so the claim is empty there
--   - encoding: real integrals ∫_{c_j}^∞ e^{−λu} F̄_j(u) du and ∫_1^∞ e^{−λBx}/x² dx → toReal of lower integrals of the nonnegative integrands; reason: both are finite (≤ 1/λ and ≤ 1)
--   - encoding: (1 − e^{−λc_j})/(λc_j) at c_j = 0 → Lean's x/0 = 0; reason: c_j = 0 forces r_j = E[X_j ∧ 0] = 0, so the term is 0 either way
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Lemma 4.5, Eq. (29), p.19 (pdf p.21)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Lemma 4.5**: for independent `X₁, …, X_m` and caps `cⱼ` with `E[Xⱼ ∧ cⱼ] = rⱼ`, for every
`λ > 0`,
`Σⱼ ∫_{cⱼ}^∞ e^{−λu} F̄ⱼ(u) du ≤ −(1/λ) ln(∫₁^∞ e^{−λBx} (1/x²) dx) − Σⱼ rⱼ (1 − e^{−λcⱼ})/(λcⱼ)` (29),
where `rⱼ = REV(Xⱼ)` and `B = BREV(X)`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Lemma 4.5, Eq. (29), p.19.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The statement is real-valued. Each integral on the left is finite (at most `1/λ`) and is
written as the `toReal` of a lower integral of a nonnegative integrand; the same for
`∫₁^∞ e^{−λBx}/x² dx ∈ (0, 1]`. `B < ∞` is assumed: when `B = ∞` the printed right side is
`+∞` (`ln 0`) and the claim is empty. `rⱼ` is finite under the caps hypothesis
(`rⱼ = E[Xⱼ ∧ cⱼ] ≤ cⱼ`). At `cⱼ = 0` the term `0/0` is Lean's `0`; there `rⱼ = 0` anyway. -/
theorem lemma_4_5 {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0)
    [∀ j, IsProbabilityMeasure (ν j)] (c : ι → ℝ≥0)
    (hc : ∀ j, ∫⁻ x, ((min x (c j) : ℝ≥0) : ℝ≥0∞) ∂(ν j) = Rev1 (ν j))
    (hB : BRev (Measure.pi ν) ≠ ⊤) (lam : ℝ) (hlam : 0 < lam) :
    ∑ j, (∫⁻ u in Set.Ioi (c j : ℝ), ENNReal.ofReal (Real.exp (-(lam * u))) * tail (ν j) u).toReal ≤
      -(1 / lam) * Real.log (∫⁻ x in Set.Ioi (1 : ℝ),
          ENNReal.ofReal (Real.exp (-(lam * (BRev (Measure.pi ν)).toReal * x)) / x ^ 2)).toReal -
        ∑ j, (Rev1 (ν j)).toReal * ((1 - Real.exp (-(lam * c j))) / (lam * c j)) := by sorry

end DetAuctions
