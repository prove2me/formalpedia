-- Prove2me | Theorems.Thm_ChenGallegoPricing_ABE_theorem_1
-- name    : ChenGallegoPricing.ABE.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:34:21.024141+00:00
-- url     : https://prove2.me/theorems/8068ef5d-813a-4d90-8bdd-c9156921344d
-- title:
--   Theorem 1 — expected regret of adaptive binning and exploration
-- statement:
--   Fix a positive integer $d$ and positive constants $M_1,M_2,M_3,M_4$. There is a constant $C>0$ such that for every measurable demand $D:[0,1)^d\times[0,1]\to[0,1]$, every Borel probability covariate law $\mu$, and every bin-law version satisfying the model's conditioning convention, if $f(x,p)=pD(x,p)$ satisfies all clauses of Assumptions 2–3 with those constants, then for every positive integer horizon $T$ and every admissible measurable ABE tie rule and split-price completion,
--   $$R_{\pi_{\mathrm{ABE}}}(T)\le C T^{(d+2)/(d+4)}(\log T)^2.$$
--
--   The policy is the concrete Algorithm 1 recursion with the exact §3.4 tuning, and regret compares to the continuous-price optimum. The covariates and fresh purchase noise have the stated independent/conditional Bernoulli laws. The constant is independent of the demand, covariate law, horizon, and choices of ties or missing prices after $d$ and the four regularity constants are fixed. The false Lemma 2 is not assumed or imported. No lower horizon threshold is imposed: in particular the assertion includes $T=1$. Insight I3 records its counterexample there; insight I2 records the algorithmic omission.
--
--   Differences from the source:
--   - generalization: C is positive and independent of T → for fixed positive d and M₁,M₂,M₃,M₄ one C works for every admissible demand, covariate law, bin-law version, horizon and measurable ABE completion; reason: the minimax formulation and constants on pp. 31–33 support uniformity; fixing an instance recovers the printed claim
--   - reading: conditional bin revenue on every rectangle, including singletons → all supported probability-law versions on null rectangles, normalized restriction on positive-mass rectangles, and Dirac laws on singletons; reason: conditioning on a null event has no canonical law; this retains arbitrary covariate laws and the stated singleton revenues
--   - reading: Algorithm 1 lines 15–22 assign no price on a splitting round → every measurable history/current-covariate-based price in [0,1] is allowed there, its usual feedback is observed but discarded from bin statistics, and exactly one split consumes the round; reason: retain every completion of the printed transition relation rather than selecting a favorable omitted action
--   - encoding: grids and thresholds are displayed even for terminal bins → only active exploration or splitting branches evaluate them; terminal bins charge their midpoint, including T=1 and T=2; reason: inactive singular metadata have no effect on any action or observation
--   - encoding: prices, covariates, revenue observations and expectations are described probabilistically → Euclidean cube and closed-unit-price subtypes, finite histories, independent covariate/uniform draws, revenue p times a threshold-generated purchase bit, and an integral of the finite sum of gaps; reason: this realizes the stated conditional Bernoulli law and equals the sum of expectations; the source’s measurability convention is explicit
--   - encoding: dyadic bins store grid spacing and empirical statistics → cells have level/integer-coordinate addresses, spacing is computed from endpoints, and histories are replayed to reconstruct the state; clipping to [0,1] only totalizes off-domain metadata; reason: reachable valid states have a unique active cell, in-range grid prices and the same counters, means and decisions
--   - reading: the ceiling glyph in §3.4 and the conflicting verbal ceiling description in the p. 26 notation table → the conventional ceiling, the smallest integer not less than its argument; reason: the formula glyph is unambiguous and the table’s smallest integer not exceeding x does not exist; insight I5 records the typo
-- source:
--   Chen and Gallego, Nonparametric Pricing Analytics with Customer Covariates, arXiv:1805.01136v3 (16 February 2020), https://arxiv.org/abs/1805.01136v3; Theorem 1, printed/PDF p. 17; standing assumptions pp. 7–11; Algorithm 1/§3.4 pp. 14–16; proof pp. 27–33

import Mathlib
import Definitions.Def_ChenGallegoPricing_ABE_Geometry
import Definitions.Def_ChenGallegoPricing_ABE_Model
import Definitions.Def_ChenGallegoPricing_ABE_Algorithm
import Definitions.Def_ChenGallegoPricing_ABE_Process

open MeasureTheory

namespace ChenGallegoPricing.ABE

theorem theorem_1 (d : ℕ)
    (hd : 0 < d)
    (M₁ M₂ M₃ M₄ : ℝ)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) (hM₄ : 0 < M₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Demand d), Measurable D →
      ∀ (μ : Measure (Ctx d)) [IsProbabilityMeasure μ]
        (ν : Set (Ctx d) → Measure (Ctx d)),
      IsBinLaw μ ν → Assumption2 D M₁ → Assumption3 D ν M₂ M₃ M₄ →
      ∀ T : ℕ, 0 < T → ∀ (tie : TieRule d) (completion : Policy d),
        IsAdmissibleABE T M₂ tie completion →
        regret D μ (abePolicy T M₂ tie completion) T ≤
          C * (T : ℝ) ^ (((d : ℝ) + 2) / ((d : ℝ) + 4)) * (Real.log T) ^ 2 := by sorry

end ChenGallegoPricing.ABE
