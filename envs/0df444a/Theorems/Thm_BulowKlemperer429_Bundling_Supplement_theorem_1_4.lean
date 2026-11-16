-- Prove2me | Theorems.Thm_BulowKlemperer429_Bundling_Supplement_theorem_1_4
-- name    : BulowKlemperer429.Bundling.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:44:04.861524+00:00
-- url     : https://prove2.me/theorems/01af8ca1-6a36-4885-8caf-cbd80659a3a6
-- title:
--   Theorem 1.4 — competition for separate selling or bundling needs $\Omega(\log m)$ bidders
-- statement:
--   There is a universal constant $c>0$ such that for every sufficiently large integer $m$ there is a product distribution $D$ on $m$ items (independent nonnegative values with finite monopoly revenue) such that for every integer $1\le k\le c\log m$,
--   $$\max\{\mathrm{SREV}_k(D),\mathrm{BREV}_k(D)\}<\mathrm{REV}(D),$$
--   where $\mathrm{SREV}_k$ and $\mathrm{BREV}_k$ are the separate-item and grand-bundle optimal auction revenues with $k$ i.i.d. bidders and $\mathrm{REV}(D)$ is the optimal revenue from one bidder.
--
--   Thus the better of separate selling and bundling needs $\Omega(\log m)$ bidders to recover one bidder's optimal revenue exactly, matching the $O(\log m)$ upper bound for separate selling.
--
--   **Formalization Note** The constant $c$ and the threshold $m_0$ are existential, in this order, and one distribution per $m$ serves every $k$ in the range; $\log$ is natural.
--
--   Differences from the source:
--   - encoding: REV(D): supremum over truthful IR mechanisms with nonnegative prices → the published Rev supremum, which also allows negative payments and asks only payment measurability; reason: the optimum is the same: IC at the zero type gives s(x) ≥ −u(0), and adding u(0) ≥ 0 to every payment keeps IC and IR and makes payments nonnegative, so the larger class has the same supremum and the strict lower bound on REV(D) means the same thing
--   - encoding: closed truthful individually rational menus → feasible IC and IR direct mechanisms on the entire nonnegative orthant with measurable payment; reason: the direct mechanism records the selected option at every type; lotteries are allowed and no allocation measurability is imposed
--   - reading: optimal single-item auction revenue REV_k with k independent draws → the published REVk: supremum over measurable feasible DSIC ex-post IR scalar auctions with nonnegative payments; reason: Appendix A p. 23 explicitly uses this auction class and says it attains or approaches optimal scalar revenue; Myerson gives the same optimum as Bayesian IC auctions; normalization to nonnegative payments is without revenue loss
--   - encoding: throughout, each marginal has finite monopoly revenue (p. 1, p. 6) → the witness satisfies postedRevenue (ν j) < ⊤ for every item, as a conjunct; reason: the standing model assumption becomes part of what the constructed distribution must satisfy
--   - encoding: for every sufficiently large integer m; integer 1 ≤ k ≤ c log m → ∃ m₀, ∀ m ≥ m₀; k : ℕ with 1 ≤ k and (k : ℝ) ≤ c · Real.log m; reason: the quantifier order ∃ c > 0, ∃ m₀, ∀ m ≥ m₀, ∃ D on exactly m items, ∀ k is the printed one; log is natural
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 3, Theorem 1.4; proof p. 21 (PDF p. 22) (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Supplement_Benchmarks
import Definitions.Def_MultiItemRev_BundlingOpt_Model
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling.Supplement

theorem theorem_1_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ ν : Fin m → Measure ℝ≥0, (∀ j, IsProbabilityMeasure (ν j)) ∧
        (∀ j, postedRevenue (ν j) < ⊤) ∧
        ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ c * Real.log m →
          max (SREVk k ν) (BREVk k ν) < MultiItemRev.BundlingOpt.Rev (Measure.pi ν) := by sorry


end BulowKlemperer429.Bundling.Supplement
