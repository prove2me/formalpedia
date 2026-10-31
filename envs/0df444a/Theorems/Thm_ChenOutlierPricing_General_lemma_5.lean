-- Prove2me | Theorems.Thm_ChenOutlierPricing_General_lemma_5
-- name    : ChenOutlierPricing.General.lemma_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:43:30.370382+00:00
-- url     : https://prove2.me/theorems/7996e302-a2d9-4f1c-ab5e-9b139c49968b
-- title:
--   Lemma 5 — simultaneous clearance and revenue-optimum price errors
-- statement:
--   Fix a model satisfying (A1)–(A2) and α>0. For every nonnegative premise failure constant Cₚ, there are C≥0 and a threshold such that the following holds uniformly for sufficiently large T, $0\le\varepsilon\le T^{-\alpha}$, any selected nonempty subset S of the T selling periods, any integer $N_3\ge2$, any Z>0, and any admissible actual run of Algorithm 4. Write $T_3=|S|$. If $\Pr\{\sum_{t\in S}\iota_t\le ZT_3\}\ge1-C_p/T^2$, then with probability at least $1-C/T^2$ both
--   $$|\widehat p^c-p^c|\le\overline L_d\left[\frac{\overline L_p(\overline p-\underline p)}{N_3}+2H_Z\right],$$
--   $$|\widehat p^o-p^o|\le\frac{2\overline L_d}{\sigma^2}\left[\frac{M\overline L_p(\overline p-\underline p)}{\sqrt2\,N_3}+\sqrt{2\overline pH_Z}\right],$$
--   where $H_Z=\min\{1,Z\}+\sqrt{N_3\log(2N_3T^2)/T_3}+2N_3\log(2N_3T^2)/T_3$. The algorithm uses actual inventory-censored sales and the printed denominator $T_0=\lceil\sqrt T\rceil$. No nondepletion premise is added. All admissible outside-S pricing rules and environments are covered, with the global absolute budget εT. The known normalization counterexample is not repaired.
--
--   Differences from the source:
--   - encoding: periods numbered 1 through T with remaining inventory → elapsed indices 0 through T-1 and recursively computed real stock; reason: a bijective time reindexing preserves every price, censored sale and revenue
--   - encoding: randomized seller policies and adaptive outlier curves with E[ξ_t | p_t] = 0 → an independent private uniform tape, arbitrary exogenous probability space, observed-history policy maps, and zero noise integrals on every price-measurable event; reason: random seeds implement stochastic decisions; integrable noise and measurable observations make the printed conditional expectation well defined without a martingale-difference or independent-noise assumption
--   - encoding: 1-O(T^-2) in premise and simultaneous conclusion → a premise coefficient Cₚ and conclusion coefficient C, quantified before T, grid, subset, Z and environment; reason: explicit uniform tail constants preserve the source asymptotic order
--   - encoding: an endpoint-inclusive grid and H_Z formulas → N₃≥2, T₃>0, T>0 and lowest-index tie selection; reason: the restrictions exclude only undefined grid/formula inputs, and fix a source-permitted tie rule
--   - encoding: Algorithm 4 selects a uniform random grid index in each selected period → exploration coordinates are disjoint from the private tape supplied to the outside policy; reason: fresh draws cannot be revealed by earlier outside-policy actions; no source execution is excluded
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, supplied source.pdf, p. 31, Lemma 5

import Definitions.Def_ChenOutlierPricing_General_Exploration

open MeasureTheory ProbabilityTheory

namespace ChenOutlierPricing.General

/-- Chen and Wang, source.pdf p. 31, Lemma 5, both simultaneous error bounds. -/
theorem lemma_5 (m : Model) (hm : Assumptions m) (α : ℝ) (hα : 0 < α) (Cprem : ℝ) (hCprem : 0 ≤ Cprem) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Tstar : ℕ, ∀ T ≥ max 1 Tstar,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (T : ℝ)^(-α) →
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.range T → 0 < S.card →
    ∀ (Z : ℝ), 0 < Z → ∀ (otherwise : Policy), PolicyAdmissible m.band otherwise →
    ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (e : Environment Ξ) (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ),
    RunAdmissible m (partialPolicy m.band S N otherwise) e T (m.x₀*T) (ε*T) μ U V →
    (1-Cprem/(T : ℝ)^2 ≤ μ.real {ω |
      corruptCount m (partialPolicy m.band S N otherwise) e T S (U ω) (V ω) ≤ Z*S.card}) →
    1-C/(T : ℝ)^2 ≤ μ.real {ω |
      let out := explorationOutput m e otherwise T N S (U ω) (V ω)
      |out.1-clearance m| ≤ clearanceErrorBound m T N S.card Z ∧
      |out.2-optimum m| ≤ optimumErrorBound m T N S.card Z} := by sorry

end ChenOutlierPricing.General
