-- Prove2me | Theorems.Thm_BoundedNVAudit_Stakes_prop5_expected_profit_full
-- name    : BoundedNVAudit.Stakes.prop5_expected_profit_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:31:41.249231+00:00
-- url     : https://prove2.me/theorems/7bfd615d-a938-404f-9c2c-39cc5077be71
-- title:
--   Proposition 5 — larger payoff scales strictly increase expected newsvendor profit
-- statement:
--   Let $f$ be a nonnegative integrable probability density on the real line with finite negative demand part. For a real price $p$ and cost $c$ with $p>c$, define
--
--   $$S=\operatorname{conv}(\operatorname{supp}f),\qquad
--   \pi(x)=p\int_{\mathbb R}\min(d,x)f(d)\,dd-cx.$$
--
--   Let $\beta>0$ and $\lambda_2<\lambda_1$ be real. For each $i=1,2$, assume that the exponential weight $e^{\lambda_i\pi/\beta}$ is integrable on $S$ and has positive integral $Z_i$, so that the behavioral order has the genuine law $\mu_i$ with density $\mathbf1_S e^{\lambda_i\pi/\beta}/Z_i$.
--
--   Truncated sales are integrable for every real order, $S$ is measurable and has positive Lebesgue measure, and $\pi$ is continuous and not almost everywhere constant on $S$. Both constructed laws are probability measures. Write $P_i=\int\max(\pi,0)\,d\mu_i$ and $N_i=\int\max(-\pi,0)\,d\mu_i$, using nonnegative extended integrals. Then
--
--   $$P_2<\infty,\qquad N_1<\infty,\qquad
--   \mathbb E_{\mu_2}\pi=P_2-N_2<P_1-N_1=\mathbb E_{\mu_1}\pi.$$
--
--   Thus neither signed expectation is an undefined difference of infinities. If $c>0$ and $\lambda_2>0$, the profit is integrable under both laws; this is a conclusion from the model data. At either endpoint, integrability under the measure is equivalent to integrability of the profit times its Lebesgue density. Whenever integrable, the signed extended expectation equals the real measure integral, which equals the published density-based real logit expectation. In particular, if both are integrable their real expected profits satisfy the same strict inequality.
--
--   This is the full source-model comparison, including signed demand and every ordered scale pair for which both behavioral laws exist. Neither payoff nonconstancy nor any behavioral payoff moment is a premise. The theorem preserves Proposition 5's strict conclusion; the minimally corrected tail-dominance reference is a supporting result only.
--
--   Differences from the source:
--   - encoding: real expected sales in (3) → finite negative demand part and a conclusion of integrable truncated sales at every real order; reason: this is exactly existence of the real truncated-sales quantities; no finite positive demand moment is needed
--   - encoding: two behavioral decisions with densities in (2) → integrable exponential weights with positive normalizers, and probability measures constructed from the published densities; reason: these express existence of the specified laws rather than a payoff moment restriction
--   - reading: the unqualified expectation notation in Proposition 5 with no payoff moment assumption → signed extended expectations with lower-law finite positive part and upper-law finite negative part, and ordinary real expectation compatibility; reason: this retains all genuine endpoint laws, excludes infinity minus infinity, and recovers the printed strict real comparison whenever integrable
--   - encoding: the profit and domain defined in §4 and used in Proposition 5 → published computed profit and convex hull of the pointwise support, with continuity, positive volume and almost everywhere nonconstancy concluded; reason: the source model must establish these properties rather than assume them; changes to interval endpoints of measure zero do not affect either law
--   - encoding: expected profits in the positive-cost positive-scale regime → both profit integrabilities follow as an additional conclusion when c and the smaller scale are positive; reason: the real expectations in that regime are justified from primitive data and are never premises of the full comparison
-- source:
--   Su, Bounded Rationality in Newsvendor Models, Manufacturing & Service Operations Management 10(4):566–589, 2008, doi:10.1287/msom.1070.0200, Proposition 5, printed p. 580 (PDF p. 15); §§3–4, printed pp. 571–572 (PDF pp. 6–7); proof printed p. 587 (PDF p. 22), equations (54)–(57)

import Mathlib
import Definitions.Def_BoundedNVAudit_Stakes_GeneralDemand
import Definitions.Def_BoundedNVAudit_Stakes_LogitLaw
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P01
import Theorems.Thm_BoundedNV_Stakes_eq54_55_single_crossing
import Theorems.Thm_BoundedNV_Stakes_eq56_57_stochastic_dominance

open MeasureTheory
open QAlgorithms.Papers.Independent.Next46.P01 (extendedExpectation)

namespace BoundedNVAudit.Stakes

/-- Su (2008), Proposition 5, printed p. 580 (PDF 15), proof p. 587 (PDF 22).
The profit and domain are computed from general real demand. Only real truncated-sales
existence and existence of the two behavioral laws are required; neither nonconstancy
nor payoff moments are hypotheses. The endpoint one-sided moments exclude undefined
infinity minus infinity. The final clauses recover the published ordinary real expectation.
The supporting (56)--(57) reference corrects the paper's false strict-everywhere tails;
the goal's strict sign is retained. -/
theorem prop5_expected_profit_full
    (f : ℝ → ℝ) (hf : IsGeneralDemandDensity f)
    (p c β lam₁ lam₂ : ℝ) (hcp : c < p) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (h₁ : LogitNormalizable (BoundedNV.ExpFam.decisionDomain f)
      (fun x => lam₁ * BoundedNV.Uniform.nvProfit f p c x) β)
    (h₂ : LogitNormalizable (BoundedNV.ExpFam.decisionDomain f)
      (fun x => lam₂ * BoundedNV.Uniform.nvProfit f p c x) β) :
    let S := BoundedNV.ExpFam.decisionDomain f
    let π := BoundedNV.Uniform.nvProfit f p c
    let μ₁ := logitMeasure S (fun x => lam₁ * π x) β
    let μ₂ := logitMeasure S (fun x => lam₂ * π x) β
    (∀ x : ℝ, Integrable (fun d => min d x * f d)) ∧
    MeasurableSet S ∧ 0 < volume S ∧ Continuous π ∧
    (¬ ∃ a : ℝ, π =ᵐ[volume.restrict S] (fun _ => a)) ∧
    IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
    (∫⁻ x, ENNReal.ofReal (π x) ∂μ₂) < ⊤ ∧
    (∫⁻ x, ENNReal.ofReal (-π x) ∂μ₁) < ⊤ ∧
    extendedExpectation μ₂ π < extendedExpectation μ₁ π ∧
    (0 < c → 0 < lam₂ → Integrable π μ₁ ∧ Integrable π μ₂) ∧
    (∀ lam ∈ ({lam₁, lam₂} : Set ℝ),
      let μ := logitMeasure S (fun x => lam * π x) β
      Integrable π μ ↔ Integrable (fun x => π x *
        BoundedNV.Uniform.logitDensity S (fun y => lam * π y) β x)) ∧
    (∀ lam ∈ ({lam₁, lam₂} : Set ℝ),
      let μ := logitMeasure S (fun x => lam * π x) β
      Integrable π μ →
        extendedExpectation μ π = ((∫ x, π x ∂μ : ℝ) : EReal) ∧
        (∫ x, π x ∂μ) = BoundedNV.Uniform.logitExp S (fun x => lam * π x) β π) ∧
    (Integrable π μ₁ → Integrable π μ₂ →
      BoundedNV.Uniform.logitExp S (fun x => lam₂ * π x) β π <
        BoundedNV.Uniform.logitExp S (fun x => lam₁ * π x) β π) := by sorry

end BoundedNVAudit.Stakes
