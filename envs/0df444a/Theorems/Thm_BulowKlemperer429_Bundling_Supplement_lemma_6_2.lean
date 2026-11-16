-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_lemma_6_2
-- name    : BulowKlemperer429.Bundling.Supplement.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:43:36.129741+00:00
-- url     : https://prove2.me/theorems/39920e10-d63b-4730-a2a6-109748e52c75
-- title:
--   Lemma 6.2 — $\max\{\mathrm{SREV}_k,\mathrm{BREV}_k\}<\mathrm{REV}$ on at most $e^{20k}$ items
-- statement:
--   For every integer $k\ge64$ there is a product distribution $D$ over $m\le e^{20k}$ items, each item value nonnegative with finite monopoly revenue, such that
--   $$\max\{\mathrm{SREV}_k(D),\mathrm{BREV}_k(D)\}<\mathrm{REV}(D).$$
--   Here $\mathrm{SREV}_k(D)=\sum_j\mathrm{REV}_k(F_j)$ sells every item through its optimal single-item auction to $k$ independent bidders, $\mathrm{BREV}_k(D)=\mathrm{REV}_k(S)$ auctions the grand bundle to $k$ independent bidders, and $\mathrm{REV}(D)$ is the optimal revenue from one bidder.
--
--   This shows that competition among $k$ bidders does not close the gap of the better simple auction when the number of items is exponential in $k$; it gives Theorem 1.4.
--
--   **Formalization Note** Revenues are extended nonnegative reals and the inequality is strict; the logarithm base is $e$.
--
--   Differences from the source:
--   - encoding: REV(D): supremum over truthful IR mechanisms with nonnegative prices → the published Rev supremum, which also allows negative payments and asks only payment measurability; reason: the optimum is the same: IC at the zero type gives s(x) ≥ −u(0), and adding u(0) ≥ 0 to every payment keeps IC and IR and makes payments nonnegative, so the larger class has the same supremum and the strict lower bound on REV(D) means the same thing
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - reading: optimal single-item auction revenue REV_k with k independent draws → the published REVk: supremum over measurable feasible DSIC ex-post IR scalar auctions with nonnegative payments; reason: Appendix A p. 23 explicitly uses this auction class and says it attains or approaches optimal scalar revenue; Myerson gives the same optimum as Bayesian IC auctions; normalization to nonnegative payments is without revenue loss
--   - encoding: throughout, each marginal has finite monopoly revenue (p. 1, p. 6) → the witness satisfies postedRevenue (ν j) < ⊤ for every item, as a conjunct; reason: the standing model assumption becomes part of what the constructed distribution must satisfy
--   - encoding: a product distribution D over at most e^{20k} items → m : ℕ with (m : ℝ) ≤ Real.exp(20k) and item laws ν : Fin m → Measure ℝ≥0; reason: the item count bound is part of the conclusion; natural exponential
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 20, Lemma 6.2 (PDF p. 21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Benchmarks
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem lemma_6_2 :
    ∀ k : ℕ, 64 ≤ k → ∃ m : ℕ, (m : ℝ) ≤ Real.exp (20 * k) ∧
      ∃ ν : Fin m → Measure ℝ≥0, (∀ j, IsProbabilityMeasure (ν j)) ∧
        (∀ j, postedRevenue (ν j) < ⊤) ∧
        max (SREVk k ν) (BREVk k ν) < MultiItemRev.BundlingOpt.Rev (Measure.pi ν) := by sorry


end BulowKlemperer429.Bundling.Supplement
