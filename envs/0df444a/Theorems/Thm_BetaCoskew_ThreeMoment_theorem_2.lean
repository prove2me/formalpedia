-- Prove2me | Theorems.Thm_BetaCoskew_ThreeMoment_theorem_2
-- name    : BetaCoskew.ThreeMoment.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:49.581438+00:00
-- url     : https://prove2.me/theorems/4d713ce1-b433-4429-bd0e-737691ceeba2
-- title:
--   Theorem 2: RDU equilibrium pricing kernel and three-moment CAPM
-- statement:
--   Consider the paper's atomless one-period market and representative agent satisfying Assumption 1. Let the market total return $\tilde R_M=\sum_i x_i^M R_i$ have a continuous CDF $F_M$, and suppose it is an equilibrium optimum of problem (P′). The pricing kernel is then determined almost surely by the market return:
--
--   $$
--   \tilde m=m(\tilde R_M)
--   =\frac{w'(1-F_M(\tilde R_M))u'(\tilde R_M)}
--     {(1+r_f)\,\mathbb E[w'(1-F_M(\tilde R_M))u'(\tilde R_M)]}.
--   $$
--
--   If $F_M$ also has a continuously differentiable density, with the stated local smoothness at total return $1$, the closed-form premiums $A$ and $B$ of (6)–(7) satisfy $A=-(1+r_f)m'(1)$ and $B=-(1+r_f)m''(1)$. Let $\rho(x)=m(1+x)-m(1)-m'(1)x-\tfrac12m''(1)x^2$, so $\rho(x)=o(x^2)$ as $x\to0$. For every asset return rate $\tilde r_i=R_i-1$ with the required finite moments, the exact three-moment pricing relation is
--
--   $$
--   \mathbb E[\tilde r_i]=r_f+A\operatorname{Cov}(\tilde r_i,\tilde r_M)
--     +\frac12 B\operatorname{Cov}(\tilde r_i,\tilde r_M^2)
--     -(1+r_f)\operatorname{Cov}(\rho(\tilde r_M),\tilde r_i),
--   \qquad \tilde r_M=\tilde R_M-1.
--   $$
--
--   The beta and coskewness terms thus have coefficients derived from utility, probability weighting, and the market-return distribution.
--
--   **Formalization Note** The paper writes the final term as $o(\tilde r_M^2)$; here it is the covariance with the fixed Taylor remainder of $m$, shared across assets. The theorem explicitly assumes local $C^3$ regularity of $u,w$, $0<F_M(1)<1$, and finite second/fourth moments in the CAPM clause. The RDU equilibrium compares payoffs whose objective is integrable and whose laws are continuous with positive payoffs almost surely. The kernel identity is proved from equilibrium, not assumed.
-- source:
--   Shi, Cui & Zhou, Beta and coskewness pricing: perspective from probability weighting, SSRN 3579960 (version of June 2, 2020), p. 11, Theorem 2, equations (4)–(7); pp. 33–35, Appendix A

import Mathlib
import Definitions.Def_BetaCoskew_ThreeMoment_Model

namespace BetaCoskew.ThreeMoment

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

/-- Theorem 2, p. 11: the equilibrium pricing kernel, its closed-form premiums,
and the three-moment CAPM with the fixed Taylor remainder. -/
theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : Atomless P)
    (u w : ℝ → ℝ) (hu : UtilityAssumption u) (hw : WeightingAssumption w)
    (rf : ℝ) (mt : Ω → ℝ) {n : ℕ} (R : Fin n → Ω → ℝ)
    (hmkt : IsPricedMarket P mt rf R)
    (xM : Fin n → ℝ) (hxM : ∑ i, xM i = 1)
    (hEq : IsEquilibrium P u w mt (fun ω => ∑ i, xM i * R i ω))
    (hF : Continuous (cdf (P.map (fun ω => ∑ i, xM i * R i ω)))) :
    let RM : Ω → ℝ := fun ω => ∑ i, xM i * R i ω
    (mt =ᵐ[P] fun ω => mFun P u w rf RM (RM ω)) ∧
    ∀ f : ℝ → ℝ, (∀ x, 0 ≤ f x) → ContDiff ℝ 1 f →
      P.map RM = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      0 < cdf (P.map RM) 1 → cdf (P.map RM) 1 < 1 →
      ContDiffAt ℝ 3 u 1 → ContDiffAt ℝ 3 w (1 - cdf (P.map RM) 1) →
      premA P u w RM f = -(1 + rf) * deriv (mFun P u w rf RM) 1 ∧
      premB P u w RM f = -(1 + rf) * iteratedDeriv 2 (mFun P u w rf RM) 1 ∧
      (rho P u w rf RM) =o[𝓝 0] (fun x : ℝ => x ^ 2) ∧
      ∀ i, MemLp (fun ω => R i ω - 1) 2 P →
        MemLp (fun ω => RM ω - 1) 4 P →
        (∫ ω, R i ω - 1 ∂P) =
          rf + premA P u w RM f *
            cov[fun ω => R i ω - 1, fun ω => RM ω - 1; P] +
          1 / 2 * premB P u w RM f *
            cov[fun ω => R i ω - 1, fun ω => (RM ω - 1) ^ 2; P] -
          (1 + rf) *
            cov[fun ω => rho P u w rf RM (RM ω - 1),
              fun ω => R i ω - 1; P] := by sorry

end BetaCoskew.ThreeMoment
