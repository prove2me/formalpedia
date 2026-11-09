-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_lemma_2_1
-- name    : BulowKlemperer429.Bundling.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:08.424275+00:00
-- url     : https://prove2.me/theorems/9a496e4b-4006-4da1-89c9-3d7cc0595a34
-- title:
--   Lemma 2.1 — all finite-revenue comparisons for k ≥ 2
-- statement:
--   Let $D$ be a finite product of $m$ nonnegative item laws, each with finite monopoly revenue. For every integer $k\ge2$,
--   $$\mathrm{BREV}(D)\le m\,\mathrm{SREV}(D)<\infty,\qquad \mathrm{BSPA}_k(D)\le\mathrm{BREV}_k(D)\le k\,\mathrm{BREV}(D).$$
--   All four comparisons, including finiteness of $m\,\mathrm{SREV}$, are asserted together. This relates posted-price benchmarks and reserve-free competition to optimal bundle auctions for every allowed bidder count.
--
--   Differences from the source:
--   - encoding: values and revenues written as nonnegative real quantities, with expectations possibly infinite → NNReal values and ENNReal revenue suprema and nonnegative integrals; reason: the representation includes unbounded laws with infinite mean and avoids the zero default of a nonintegrable Bochner integral
--   - reading: optimal single-item auction revenue with k draws → supremum over measurable feasible DSIC ex-post IR scalar auctions with nonnegative payments; reason: Appendix A p. 23 explicitly uses this auction class and says it attains or approaches optimal scalar revenue; Myerson gives the same optimum as Bayesian IC auctions; normalization to nonnegative payments is without revenue loss
--   - encoding: m items and integer k ≥ 2 → a finite index type of cardinality m and a natural number k with 2 ≤ k; reason: this ranges over precisely the nonnegative integer counts used by the source, with the harmless empty-item case also satisfying the inequalities
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, Lemma 2.1; proof Appendix A p. 22 (PDF p. 23) (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_ScalarAuction
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

theorem lemma_2_1 {ι : Type} [Fintype ι]
    (ν : ι → Measure ℝ≥0) [∀ j, IsProbabilityMeasure (ν j)]
    (hfinite : ∀ j, postedRevenue (ν j) < ⊤) (k : ℕ) (hk : 2 ≤ k) :
    BREV ν ≤ (Fintype.card ι : ℝ≥0∞) * SREV ν ∧
    (Fintype.card ι : ℝ≥0∞) * SREV ν < ⊤ ∧
    BSPA k ν ≤ BREVk k ν ∧ BREVk k ν ≤ (k : ℝ≥0∞) * BREV ν := by sorry

end BulowKlemperer429.Bundling
