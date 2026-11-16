-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_6_1
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:42:48.725466+00:00
-- url     : https://prove2.me/theorems/426a507b-c6ff-4eb2-8d74-e38abe6849b4
-- title:
--   Lemma 6.1 — marginal-mechanism bound for $\mathrm{REV}_k(X+Y)$
-- statement:
--   Let $X$ and $Y$ be independent nonnegative random variables and let $k$ bidders have independent values distributed as $X+Y$. Let $\mathrm{REV}_k(F)$ be the optimal single-item auction revenue with $k$ independent bidders drawn from $F$, and $\mathrm{REV}(X)=\sup_{t\ge0}t\Pr[X\ge t]$. Then
--   $$\mathrm{REV}_k(X+Y)\le\mathrm{REV}_k(X)+\mathbb E\Big[\max_{i\le k}Y_i\Big]\le k\,\mathrm{REV}(X)+\mathbb E\Big[\max_{i\le k}Y_i\Big],$$
--   where $Y_1,\dots,Y_k$ are independent copies of $Y$.
--
--   This is the marginal-mechanism bound of [BILW20, Lemma 1]; it limits grand-bundle revenue with $k$ bidders in the construction of Lemma 6.2.
--
--   **Formalization Note** $\mathrm{REV}_k$ is the supremum over measurable, feasible, dominant-strategy truthful, ex-post individually rational scalar auctions with nonnegative payments. The expectation of the maximum is a $[0,\infty]$-valued integral (zero for $k=0$).
--
--   Differences from the source:
--   - reading: optimal single-item auction revenue REV_k with k independent draws → the published REVk: supremum over measurable feasible DSIC ex-post IR scalar auctions with nonnegative payments; reason: Appendix A p. 23 explicitly uses this auction class and says it attains or approaches optimal scalar revenue; Myerson gives the same optimum as Bayesian IC auctions; normalization to nonnegative payments is without revenue loss
--   - encoding: values and revenues written as nonnegative real quantities, with expectations possibly infinite → NNReal values and ENNReal revenue suprema and nonnegative integrals; reason: the representation includes unbounded laws with infinite mean and avoids the zero default of a nonintegrable Bochner integral
--   - encoding: X and Y independent with values X + Y for each bidder; E[max_{i≤k} Y_i] over independent copies → the bidder value law is the pushforward of μX ⊗ μY by addition; the expectation is a [0,∞]-valued lintegral over Measure.pi of k copies of μY of ⨆_i Y_i; reason: independence makes the law of X + Y the convolution; the extended integral allows infinite means
--   - generalization: k independent bidders (k ≥ 1) → every k : ℕ, including k = 0; reason: for k = 0 both sides are 0; for k ≥ 1 the statement is the source's
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 20, Lemma 6.1; proof Appendix A p. 23 (PDF p. 24) (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_ScalarAuction
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_6_1 (μX μY : Measure ℝ≥0) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (k : ℕ) :
    REVk k ((μX.prod μY).map (fun z => z.1 + z.2)) ≤
        REVk k μX + ∫⁻ y, ⨆ i, (y i : ℝ≥0∞) ∂Measure.pi (fun _ : Fin k => μY) ∧
      REVk k μX + ∫⁻ y, ⨆ i, (y i : ℝ≥0∞) ∂Measure.pi (fun _ : Fin k => μY) ≤
        (k : ℝ≥0∞) * postedRevenue μX +
          ∫⁻ y, ⨆ i, (y i : ℝ≥0∞) ∂Measure.pi (fun _ : Fin k => μY) := by sorry


end BulowKlemperer429.Bundling.Supplement
