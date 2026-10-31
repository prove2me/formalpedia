-- Prove2me | Theorems.Thm_ChenOutlierPricing_General_corollary_EC1
-- name    : ChenOutlierPricing.General.corollary_EC1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:44:46.661137+00:00
-- url     : https://prove2.me/theorems/e4060449-8278-4d72-88d1-a4c6b7957dd5
-- title:
--   Corollary EC.1 — price consistency relative to the inventory-regime gap
-- statement:
--   For fixed positive exponents β′>γ′>0 there exists a polynomial $\phi(\log T,\overline L_d,\overline L_p,\overline p,1/|p^o-p^c|)$, whose degrees depend only on those exponents, with the following property. In any model satisfying (A1)–(A3), $p^c\ne p^o$, consider Algorithm 4 with the exact equalities $T_3=T^{\beta'}$, $N_3=T^{\gamma'}$ (integer counts) and
--   $$0<Z\le\tfrac13\max\left\{\frac{|p^o-p^c|}{40\overline L_d},\frac1{2\overline p}\left(\frac{\sigma^2|p^o-p^c|}{40\overline L_d}\right)^2\right\}.$$
--   Assume the Lemma 5 contamination event has probability at least $1-C_p/T^2$. If $T\ge\phi$, then with probability at least $1-C/T^2$,
--   $$|\widehat p^c-p^c|+|\widehat p^o-p^o|\le0.2|p^o-p^c|.$$
--   For each fixed model, α and Cₚ, the failure coefficient C precedes T, ε, Z, the selling subset and the environment. The source's maximum, exact power equalities, five polynomial arguments, and constant 0.2 are retained. No rounding relaxation or correction of the threshold is made.
--
--   Differences from the source:
--   - encoding: periods numbered 1 through T with remaining inventory → elapsed indices 0 through T-1 and recursively computed real stock; reason: a bijective time reindexing preserves every price, censored sale and revenue
--   - encoding: randomized seller policies and adaptive outlier curves with E[ξ_t | p_t] = 0 → an independent private uniform tape, arbitrary exogenous probability space, observed-history policy maps, and zero noise integrals on every price-measurable event; reason: random seeds implement stochastic decisions; integrable noise and measurable observations make the printed conditional expectation well defined without a martingale-difference or independent-noise assumption
--   - encoding: a polynomial of five displayed variables with exponent-dependent degrees → one multivariate polynomial in Fin 5 chosen after β′, γ′ and before model and horizon; reason: the five coordinates are exactly the printed arguments, and no extra dependence or rounding of power equalities is introduced
--   - encoding: 1-O(T^-2) and Algorithm 4 outputs → uniform explicit failure coefficients and the same defined-grid domain and tie convention as Lemma 5; reason: the original probability order and both error terms are preserved
--   - encoding: Algorithm 4 selects a uniform random grid index in each selected period → exploration coordinates are disjoint from the private tape supplied to the outside policy; reason: fresh draws cannot be revealed by earlier outside-policy actions; no source execution is excluded
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, e-companion, p. ec15, Corollary EC.1

import Definitions.Def_ChenOutlierPricing_General_Bounds

open MeasureTheory ProbabilityTheory

namespace ChenOutlierPricing.General

/-- Chen and Wang, e-companion ec15, Corollary EC.1; printed max retained. -/
theorem corollary_EC1 (β γ : ℝ) (hγ : 0 < γ) (hβ : γ < β) :
    ∃ φ : MvPolynomial (Fin 5) ℝ,
    ∀ α : ℝ, 0 < α → ∀ (m : Model), Assumptions m → clearance m ≠ optimum m →
    ∀ Cprem : ℝ, 0 ≤ Cprem → ∃ C : ℝ, 0 ≤ C ∧
    ∀ T : ℕ, 0 < T → (T : ℝ) ≥ MvPolynomial.eval (corollaryParameters m T) φ →
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ (T : ℝ)^(-α) →
    ∀ (N : ℕ) (S : Finset ℕ), 2 ≤ N → S ⊆ Finset.range T →
      (S.card : ℝ) = (T : ℝ)^β → (N : ℝ) = (T : ℝ)^γ →
    ∀ Z : ℝ, 0 < Z → Z ≤ corollaryThreshold m →
    ∀ otherwise : Policy, PolicyAdmissible m.band otherwise →
    ∀ {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ]
      (e : Environment Ξ) (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ),
    RunAdmissible m (partialPolicy m.band S N otherwise) e T (m.x₀*T) (ε*T) μ U V →
    (1-Cprem/(T : ℝ)^2 ≤ μ.real {ω |
      corruptCount m (partialPolicy m.band S N otherwise) e T S (U ω) (V ω) ≤ Z*S.card}) →
    1-C/(T : ℝ)^2 ≤ μ.real {ω |
      let out := explorationOutput m e otherwise T N S (U ω) (V ω)
      |out.1-clearance m| + |out.2-optimum m| ≤ (1/5 : ℝ)*|optimum m-clearance m|} := by sorry

end ChenOutlierPricing.General
