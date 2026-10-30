-- Prove2me | Theorems.Thm_DataDrivenRO_KSFull_theorem_5
-- name    : DataDrivenRO.KSFull.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:57.46736+00:00
-- url     : https://prove2.me/theorems/1e838679-8280-49eb-8459-f206daffe231
-- title:
--   Theorem 5 — simultaneous KS sampling guarantee and support formula
-- statement:
--   Let $d,N\ge1$, let $P^*$ be a Borel probability law on $\mathbb R^d$ with independent coordinates, and let $lo\le hi$ be the endpoints of a known finite box with $P^*([lo,hi])=1$. Fix $0<\alpha<1$. Draw $S=(\hat u^1,\ldots,\hat u^N)$ with the actual law $(P^*)^N$, sort each coordinate increasingly with multiplicity, and pad by $lo_i,hi_i$. Set $\beta=1-(1-\alpha)^{1/d}$ and let $\Gamma=\Gamma^{KS}(N,\beta)$ be the exact uniform-statistic quantile defined in the accompanying module.
--
--   Write $q^L,q^R$ for the vectors (17): for $k=\lfloor N(1-\Gamma)\rfloor$, $q^L$ has masses $\Gamma$, then $1/N$ at indices $1,\ldots,k$, residual $1-\Gamma-k/N$ at $k+1$, and zero elsewhere; $q^R$ reverses it. The set used throughout is exactly (18):
--   $$
--   \mathcal U^I_\epsilon(S)=\left\{u:\exists\theta_i\in[0,1],\ q^i\in\Delta_{N+2},\quad
--   u_i=\sum_{j=0}^{N+1}\hat u_i^{(j)}q_j^i\ (i=1,\ldots,d),\quad
--   \sum_i D(q^i,\theta_iq^L+(1-\theta_i)q^R)\le\log(1/\epsilon)\right\}.
--   $$
--   Here $D$ is relative entropy, zero summands are retained, and missing base support gives infinite divergence. The finite vectors in this definition do not restrict $P^*$ to a discrete law.
--
--   The conclusion has the following clauses.
--
--   1. The marginal level lies in $(0,1)$ and $(1-\beta)^d=1-\alpha$. The critical value lies in $(0,1)$ and is the least real threshold whose uniform-statistic acceptance probability is at least $1-\beta$. For every Borel probability law $Q$ on the real line, the two-sided acceptance event using $Q(({-\infty},s_{(j)}])$ in the lower constraint and $Q(({-\infty},s_{(j)}))$ in the upper constraint is measurable and has probability at least $1-\beta$ under $Q^N$. Atomic and unbounded marginal laws are included in this marginal-calibration assertion.
--   2. There is a measurable sample event $E$, equal to supported samples accepted in every marginal, on which $P^*\in\mathcal P^I(S)$, such that
--   $$
--   (P^*)^N(E)\ge1-\alpha.
--   $$
--   For every $S\in E$, simultaneously for every $0<\epsilon<1$, every decision dimension $m$, every real-valued $f:\mathbb R^d\times\mathbb R^m\to\mathbb R$ concave in $u$ for every decision, and every $x^*\in\mathbb R^m$,
--   $$
--   [\forall u\in\mathcal U^I_\epsilon(S),\ f(u,x^*)\le0]
--   \ \Longrightarrow\ P^*\{u:f(u,x^*)\le0\}\ge1-\epsilon.
--   $$
--   The outer probability is over the data; the inner probability is under $P^*$. The event is common to every level, function and decision.
--   3. For every supported sample, every $0<\epsilon<1$ and every $v\in\mathbb R^d$, the uncertainty set is nonempty, convex and compact and
--   $$
--   \delta^*(v\mid\mathcal U^I_\epsilon(S))=
--   \inf_{\lambda>0}\left\{\lambda\log(1/\epsilon)+\lambda\sum_i\log\max\left(
--   \sum_{j=0}^{N+1}q_j^L e^{v_i\hat u_i^{(j)}/\lambda},
--   \sum_{j=0}^{N+1}q_j^R e^{v_i\hat u_i^{(j)}/\lambda}\right)\right\}.
--   $$
--   This is the value in (19) with its closed-perspective zero boundary; no positive minimizer is asserted. The support identity applies even to supported samples outside $E$.
--
--   This theorem connects exact finite-sample hypothesis testing to the robust guarantee for all concave constraints, and identifies the support of the same entropy set. Coverage, geometry and the support identity are conclusions, not premises. No density, atomlessness, strict sorting, or finite-support condition is added.
--
--   Differences from the source:
--   - reading: p. 15 says jth largest although its ranks and endpoints use increasing order → the jth smallest observation with multiplicity; reason: the CDF constraints, (17), and (EC.4) determine the increasing-order convention
--   - encoding: iid observations in a known finite box with independent components → Fin-indexed real vectors, the actual finite product sampling law, coordinate independence, and zero mass outside the closed box; reason: these are the same Borel laws and samples, including atomic laws and degenerate box intervals
--   - encoding: the tabulated exact KS threshold at marginal significance and the validity of the test → the uniform-order-statistic quantile with range, quantile attainment, marginal acceptance and calibration arithmetic as explicit conclusions; reason: this specifies the exact threshold and exposes its correctness obligations without assuming coverage
--   - encoding: with sampling probability at least 1−α the entire family simultaneously implies (P2) → an explicitly measurable witnessing event equal to supported all-marginal acceptance, with confidence-region membership and the full all-level concave-constraint guarantee; reason: an actual sampling probability and its common event are made explicit; neither outer-measure-only evidence nor a fixed-level event is substituted
--   - encoding: relative entropy with infinite divergence at missing support → the unchanged published UI with AbsCont and real relEntropy; reason: the entropy radius is finite, so this is equivalent and preserves all zero-mass cases
--   - encoding: support formula (19) with the closed perspective at λ≥0 → IsGLB over positive λ together with nonempty convex compactness of the same set; reason: the positive-domain infimum has the same closed-perspective value and need not be attained; the geometry makes the real support supremum genuine
--   - generalization: §5.1 works with marginals carried by the known finite box → the auxiliary marginal-calibration conclusion also quantifies over unbounded Borel probability laws on ℝ; reason: the same uniform-quantile test and closed/left-CDF inequalities are valid without a support bound; specializing Q to each bounded source marginal recovers every source instance
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, https://arxiv.org/abs/1401.0212v2, Theorem 5, (18)–(19), p. 16 (PDF 16); standing assumptions §§1.1 and 5.1, pp. 6,15; (P2)/(2), p. 2; simultaneous definition pp. 11–12; proof EC.1.4, pp. ec3–ec4 (PDF 41–42).

import Mathlib
import Definitions.Def_DataDrivenRO_KSFull_Setting

open MeasureTheory

namespace DataDrivenRO.KSFull

/-- Full Theorem 5, (18)–(19), arXiv:1401.0212v2, p. 16 (proof ec3–ec4).
Exact KS calibration and arbitrary-law marginal validity are conclusions, never assumptions.
The single measurable event is uniform over every violation level and every concave constraint.
The deterministic support identity holds for ALL supported samples, not just that event.
The IsGLB over positive multipliers gives the infimum of the closed perspective at λ≥0. -/
theorem theorem_5 {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    (Pstar : Measure (Fin d → ℝ)) [IsProbabilityMeasure Pstar]
    (hind : ProbabilityTheory.iIndepFun (fun i : Fin d => fun u : Fin d → ℝ => u i) Pstar)
    (lo hi : Fin d → ℝ) (hbox : lo ≤ hi)
    (hsupp : Pstar (Set.Icc lo hi)ᶜ = 0)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    let β := marginalLevel d α
    let Γ := criticalValue N β
    (0 < β ∧ β < 1 ∧ (1 - β) ^ d = 1 - α) ∧
    (0 < Γ ∧ Γ < 1 ∧
      IsLeast {t : ℝ | ENNReal.ofReal (1 - β) ≤
        uniformSampleLaw N {s | uniformStatistic s ≤ t}} Γ) ∧
    (∀ Q : Measure ℝ, IsProbabilityMeasure Q →
      MeasurableSet (marginalAcceptance (N := N) Q Γ) ∧
      ENNReal.ofReal (1 - β) ≤
        Measure.pi (fun _ : Fin N => Q) (marginalAcceptance Q Γ)) ∧
    (∃ E : Set (Fin N → Fin d → ℝ), E = goodEvent Pstar lo hi α ∧
      MeasurableSet E ∧ ENNReal.ofReal (1 - α) ≤ sampleLaw Pstar N E ∧
      ∀ S ∈ E, S ∈ supportedSamples lo hi ∧ Pstar ∈ confidenceRegion lo hi α S ∧
        Guarantee.SimultaneouslyImpliesGuarantee Pstar (uncertaintySet lo hi α S)) ∧
    (∀ S ∈ supportedSamples (N := N) lo hi, ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
      (uncertaintySet lo hi α S ε).Nonempty ∧
      Convex ℝ (uncertaintySet lo hi α S ε) ∧
      IsCompact (uncertaintySet lo hi α S ε) ∧
      ∀ v : Fin d → ℝ,
        IsGLB ((fun lam => KS.boundKS (paddedOrder lo hi S) Γ ε v lam) '' Set.Ioi 0)
          (RobustMDP.Shared.supportFunction (uncertaintySet lo hi α S ε) v)) := by sorry

end DataDrivenRO.KSFull
