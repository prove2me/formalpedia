-- Prove2me | Theorems.Thm_DetAuctions_eq_20
-- name    : DetAuctions.eq_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:17:22.93607+00:00
-- url     : https://prove2.me/theorems/67267c1f-96cd-4c64-8bce-3390cb79c4ca
-- title:
--   Eq. (20) — the residual expectation as an integral of capped tails
-- statement:
--   Let $X_1,\dots,X_m$ be independent nonnegative random variables, $c_1,\dots,c_m\ge0$ caps, $Y_j=(X_j-c_j)_+$ and $\bar F_j^{c_j}(t)=\mathrm{Prob}[X_j>c_j+t]=\mathrm{Prob}[Y_j>t]$. Then
--   $$\mathbb E\Big[\sum_{j=1}^m Y_j-\max_{j}Y_j\Big]=\int_0^\infty\Big[\sum_{j=1}^m\mathrm{Prob}[Y_j>t]-\mathrm{Prob}\big[\max_j Y_j>t\big]\Big]dt$$
--   $$=\int_0^\infty\Big[\sum_{j=1}^m\bar F_j^{c_j}(t)-1+\prod_{j=1}^m\mathrm{Prob}[Y_j\le t]\Big]dt=\int_0^\infty\Big[\sum_{j=1}^m\bar F_j^{c_j}(t)-1+\prod_{j=1}^m\big(1-\bar F_j^{c_j}(t)\big)\Big]dt.$$
--
--   This tail-integral form of the residual term of the master inequality is what the paper bounds in all its approximation results.
--
--   **Formalization Note** The model is the published `MultiItemRev.Decomp`: values in $\mathbb R_+^m$ (`ι → ℝ≥0`), mechanisms $(a,p)$ with $a\in[0,1]^m$, (DSIC) and (IR) on all of $\mathbb R_+^m$ and a measurable payment; $\mathsf{REV}$ is the supremum of $\mathbb E[p(X)]$ over all of them (lotteries included), in $[0,\infty]$. Independent items are the product of probability laws $F_j$ on $[0,\infty)$. All three integrands are nonnegative; the equalities hold in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: independent X_j ∼ F_j, real revenues → product law Measure.pi ν of probability laws ν j on ℝ≥0; revenues in ℝ≥0∞; reason: same instances; an unbounded law may have revenue +∞, where the inequalities read in [0, ∞]
--   - encoding: ∫ over (0, ∞) (or (c_j, ∞)) of a nonnegative integrand → lower integral of ENNReal.ofReal of the integrand over Set.Ioi, in ℝ≥0∞; reason: the integrands are nonnegative, so ofReal loses nothing and the value +∞ is kept
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], §4, Eq. (20), p.15 (pdf p.17)

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model
import Definitions.Def_DetAuctions_tail
import Definitions.Def_DetAuctions_excessResidual

open MeasureTheory MultiItemRev.Decomp
open scoped NNReal ENNReal

namespace DetAuctions

/-- **Eq. (20)**: for independent values and individual caps `cⱼ`, with `Yⱼ = (Xⱼ − cⱼ)₊` and
`F̄ⱼ^{cⱼ}(t) = Prob[Xⱼ > cⱼ + t] = Prob[Yⱼ > t]`,
`E[Σⱼ Yⱼ − maxⱼ Yⱼ] = ∫₀^∞ [Σⱼ Prob[Yⱼ > t] − Prob[maxⱼ Yⱼ > t]] dt
 = ∫₀^∞ [Σⱼ F̄ⱼ^{cⱼ}(t) − 1 + Πⱼ Prob[Yⱼ ≤ t]] dt = ∫₀^∞ [Σⱼ F̄ⱼ^{cⱼ}(t) − 1 + Πⱼ (1 − F̄ⱼ^{cⱼ}(t))] dt`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), §4, Eq. (20), p.15.

**Formalization Note** The model is the published `MultiItemRev.Decomp`: item values in `ι → ℝ≥0`, mechanisms
`(q, s)` with allocation in `[0,1]` per item, DSIC and IR on all of `ℝ₊^m` and a measurable
payment; `Rev` is the supremum of the expected payment (an `EReal`, mapped to `ℝ≥0∞`) over all
such mechanisms, `Rev1 ν` the one-item revenue of a law `ν`, `SRev μ = Σⱼ Rev1 (μⱼ)` and
`BRev μ = Rev1 (law of Σⱼ Xⱼ)`. Independent items are the product law `Measure.pi ν` of
probability laws `ν j` on `ℝ≥0`.
The caps are arbitrary `cⱼ ≥ 0`. The three integrands are nonnegative (the event
`{maxⱼ Yⱼ > t}` is the union of the `{Yⱼ > t}`, and `Σ xⱼ − 1 + Π(1 − xⱼ) ≥ 0` on `[0,1]^m`),
so they are integrated as `ENNReal.ofReal` of the real integrand over `(0, ∞)`, and the
equalities hold in `ℝ≥0∞` (all members may be `+∞`). Probabilities enter through `toReal`,
which is exact for a probability measure. -/
theorem eq_20 {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)]
    (c : ι → ℝ≥0) :
    (∫⁻ x, (excessResidual c x : ℝ≥0∞) ∂(Measure.pi ν) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∑ j, (Measure.pi ν {x | t < ((x j - c j : ℝ≥0) : ℝ)}).toReal -
          (Measure.pi ν {x | t < ((Finset.univ.sup (fun j => x j - c j) : ℝ≥0) : ℝ)}).toReal)) ∧
    (∫⁻ x, (excessResidual c x : ℝ≥0∞) ∂(Measure.pi ν) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∑ j, (tail (ν j) ((c j : ℝ) + t)).toReal - 1 +
          ∏ j, (Measure.pi ν {x | ((x j - c j : ℝ≥0) : ℝ) ≤ t}).toReal)) ∧
    (∫⁻ x, (excessResidual c x : ℝ≥0∞) ∂(Measure.pi ν) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (∑ j, (tail (ν j) ((c j : ℝ) + t)).toReal - 1 +
          ∏ j, (1 - (tail (ν j) ((c j : ℝ) + t)).toReal))) := by sorry

end DetAuctions
