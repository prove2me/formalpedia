-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_10
-- name    : ClassifAgg.Aggregation.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:32.626448+00:00
-- url     : https://prove2.me/theorems/317c4d80-6484-467b-baf8-e7e3aaca8c27
-- title:
--   Lemma 10, p. 164 — P(W_0n(𝒢) ≥ x n^{−1/(1+ρ)}) ≤ Q₁ exp(−Q₂ n^{ρ/(1+ρ)}) for all x ≥ Q₃
-- statement:
--   Let $A>0$ and $0<\rho_{\min}<\rho_{\max}<1$, and let $c_1>0$. There exist $Q_1>0$, $Q_2>0$, $Q_3>0$, depending only on $A,\rho_{\min},\rho_{\max}$ and $c_1$, with the following property.
--
--   Let $n\ge1$, let $\pi=(P_X,\eta)$ be a distribution of $(X,Y)$, let $\rho\in[\rho_{\min},\rho_{\max}]$, and let $\mathcal G$ be a class of Borel sets having complexity bound $\rho$ with constant $A$ for $d_\triangle$, with $G^*\in\mathcal G$. Then
--   $$P_{\pi,n}\big(W_{0n}(\mathcal G)\ge xn^{-1/(1+\rho)}\big)\le Q_1\exp\big(-Q_2n^{\rho/(1+\rho)}\big)\qquad\forall\,x\ge Q_3,$$
--   where $W_{0n}(\mathcal G)=\sup\{d_{\triangle,e}(G,G'):G,G'\in\mathcal G,\ d_\triangle(G,G')\le c_1n^{-1/(1+\rho)}\}$.
--
--   Pairs of sets that are close for $d_\triangle$ remain close for the empirical distance; this is used in the proof of Lemma 5.
--
--   **Formalization Note** On the page $c_1$ is the constant of Lemma 7; the statement holds for every $c_1>0$, with constants that may depend on it, which contains the page's case. The standing assumptions are hypotheses, and the probability is the outer measure of the event.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, Lemma 10, p. 164

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Suprema
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_10 (A ρmin ρmax : ℝ) (hA : 0 < A) (hρmin : 0 < ρmin) (hρ : ρmin < ρmax) (hρmax : ρmax < 1) :
    ∀ c1 : ℝ, 0 < c1 → ∃ Q1 Q2 Q3 : ℝ, 0 < Q1 ∧ 0 < Q2 ∧ 0 < Q3 ∧
      ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (PX : Measure (E d)) (η : E d → ℝ), IsDistr (PX, η) →
      ∀ cls : Set (Set (E d)), (∀ G ∈ cls, MeasurableSet G) →
      ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ ρmax → HasComplexityBound PX cls ρ A → bayesSet η ∈ cls →
      ∀ x : ℝ, Q3 ≤ x →
      sampleLaw PX η n {s | x * (n : ℝ) ^ (-1 / (1 + ρ)) ≤ W0sup c1 ρ PX cls s}
        ≤ ENNReal.ofReal (Q1 * Real.exp (-Q2 * (n : ℝ) ^ (ρ / (1 + ρ)))) := by sorry

end ClassifAgg.Aggregation
