-- Prove2me | Theorems.Thm_ConsumerUtilityApprox_UnitDemand_posted_price_representation
-- name    : ConsumerUtilityApprox.UnitDemand.posted_price_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:35.448006+00:00
-- url     : https://prove2.me/theorems/44ba9c47-24eb-42e5-88ea-254539fee49c
-- title:
--   §2.3 / Appendix C.1 — OPT^{1,1}(X; q) is attained by a posted price drawn from at most two (possibly infinite) prices
-- statement:
--   Let $X\ge0$ have law $\nu$ with finite mean and let $q\in[0,1]$. Then the single-dimensional benchmark
--   $$\mathrm{OPT}^{1,1}(X;q)=\sup\{\mathbb E[Xa(X)-\tau(X)]:(a,\tau)\text{ BIC and IR},\ \tau\ge0,\ \mathbb E[a(X)]\le q\}$$
--   is attained by a posted price $P$ drawn independently of $X$ from at most two options $p_1,p_2\in[0,\infty]$ (probabilities $\theta,1-\theta$, $\theta\in[0,1]$; $\infty$ = no offer; sale iff $X>P$): $\Pr(X>P)\le q$ and $\mathbb E[(X-P)^+]=\mathrm{OPT}^{1,1}(X;q)$. This is what the pricing branch of every mechanism uses, and it is what makes an $\mathrm{OPT}^{1,1}$ oracle of §2.4 exist.
--
--   Differences from the source:
--   - encoding: OPT^{1,1}(X; q) is a max, used both for the optimal mechanism and its value → OPT11 is the supremum; the statement asserts a two-point price law attaining it; reason: the attaining posted-price law is itself a BIC, IR mechanism, so the supremum is a maximum
--   - reading: BIC and IR mechanisms (a, τ) (rules tacitly measurable) → SDMechanism.IsAdmissible includes measurability of a and τ; reason: expectations are otherwise undefined
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 8, §2.3 (characterization sketched in Appendix C.1, pp. 38–39)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MultiItemRev.BundlingOpt

namespace ConsumerUtilityApprox.UnitDemand

theorem posted_price_representation (ν : ProbabilityMeasure ℝ≥0) (hν : HasFiniteMean ν)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ P : TwoPointPrice, 0 ≤ P.θ ∧ P.θ ≤ 1 ∧ IsImplementing ν q P := by sorry

end ConsumerUtilityApprox.UnitDemand
