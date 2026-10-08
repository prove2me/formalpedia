-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_7
-- name    : ClassifAgg.Aggregation.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:23.240072+00:00
-- url     : https://prove2.me/theorems/a62fe7a8-6167-4e67-83c4-e47ac199ad4f
-- title:
--   Lemma 7, p. 163 — P(W_n(𝒢) ≥ 1/2) ≤ A₁ exp(−A₂ n^{ρ/(1+ρ)})
-- statement:
--   Let $A>0$ and $0<\rho_{\min}<\rho_{\max}<1$. There exist constants $c_1>0$, $A_1>0$, $A_2>0$, depending only on $A,\rho_{\min},\rho_{\max}$, with the following property.
--
--   Let $n\ge1$, let $\pi=(P_X,\eta)$ be a distribution of $(X,Y)$ on $\mathbb R^d\times\{0,1\}$, let $\rho\in[\rho_{\min},\rho_{\max}]$, and let $\mathcal G$ be a class of Borel sets having complexity bound $\rho$ with constant $A$ for $d_\triangle$, with $G^*=\{\eta\ge1/2\}\in\mathcal G$. Then, with $W_n(\mathcal G)$ built with this $c_1$,
--   $$P_{\pi,n}\Big(W_n(\mathcal G)\ge\tfrac12\Big)\le A_1\exp\big(-A_2n^{\rho/(1+\rho)}\big).$$
--
--   The lemma says that, uniformly over pairs of sets at $d_\triangle$-distance at least $c_1n^{-1/(1+\rho)}$, the empirical distance $d_{\triangle,e}$ is comparable to $d_\triangle$ with overwhelming probability. It is used in the proofs of Lemmas 1 and 5.
--
--   **Formalization Note** The Appendix's standing assumptions ("$\mathcal G$ has complexity bound $\rho\in[\rho_{\min},\rho_{\max}]$, $0<\rho_{\min}<\rho_{\max}<1$, $G^*\in\mathcal G$", p. 163) are hypotheses. The constants are chosen before the dimension, the sample size, the distribution, the class and $\rho$. The probability of the event is its outer measure under the sample law, since the supremum over an uncountable class need not be measurable.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, Lemma 7, p. 163

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Suprema
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_7 (A ρmin ρmax : ℝ) (hA : 0 < A) (hρmin : 0 < ρmin) (hρ : ρmin < ρmax) (hρmax : ρmax < 1) :
    ∃ c1 A1 A2 : ℝ, 0 < c1 ∧ 0 < A1 ∧ 0 < A2 ∧
      ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (PX : Measure (E d)) (η : E d → ℝ), IsDistr (PX, η) →
      ∀ cls : Set (Set (E d)), (∀ G ∈ cls, MeasurableSet G) →
      ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ ρmax → HasComplexityBound PX cls ρ A → bayesSet η ∈ cls →
      sampleLaw PX η n {s | 1 / 2 ≤ Wsup c1 ρ PX cls s}
        ≤ ENNReal.ofReal (A1 * Real.exp (-A2 * (n : ℝ) ^ (ρ / (1 + ρ)))) := by sorry

end ClassifAgg.Aggregation
