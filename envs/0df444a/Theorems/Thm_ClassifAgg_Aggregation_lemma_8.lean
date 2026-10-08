-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_8
-- name    : ClassifAgg.Aggregation.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:15:40.643338+00:00
-- url     : https://prove2.me/theorems/df5cc762-4fe0-4882-8134-a7a41cf16aa6
-- title:
--   Lemma 8, p. 164 — P(V_n(𝒢) ≥ x) ≤ D₁ exp(−D₂x) for all x ≥ D₃
-- statement:
--   Let $A>0$ and $0<\rho_{\min}<\rho_{\max}<1$, and let $c_1>0$. There exist $D_1>0$, $D_2>0$, $D_3>0$, depending only on $A,\rho_{\min},\rho_{\max}$ and $c_1$, with the following property.
--
--   Let $n\ge1$, let $\pi=(P_X,\eta)$ be a distribution of $(X,Y)$, let $\rho\in[\rho_{\min},\rho_{\max}]$, and let $\mathcal G$ be a class of Borel sets having complexity bound $\rho$ with constant $A$ for $d_\triangle$, with $G^*\in\mathcal G$. Then
--   $$P_{\pi,n}\big(V_n(\mathcal G)\ge x\big)\le D_1\exp(-D_2x)\qquad\forall\,x\ge D_3,$$
--   where
--   $$V_n(\mathcal G)=\sup_{G\in\mathcal G:\ d_\triangle(G,G^*)\ge c_1n^{-1/(1+\rho)}}\frac{\sqrt n\,|R_n(G^*)-R_n(G)+d(G,G^*)|}{d_\triangle^{(1-\rho)/2}(G,G^*)}.$$
--
--   This weighted bound on the empirical excess risk drives the rates of Theorem 1 and Theorem 3.
--
--   **Formalization Note** On the page $c_1$ is the constant of Lemma 7, which depends only on $A,\rho_{\min},\rho_{\max}$. The statement here holds for every $c_1>0$, with constants that may also depend on $c_1$; it contains the page's case and is what the proofs use. The Appendix's standing assumptions are hypotheses, and the probability is the outer measure of the event.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, Lemma 8, p. 164

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Suprema
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_8 (A ρmin ρmax : ℝ) (hA : 0 < A) (hρmin : 0 < ρmin) (hρ : ρmin < ρmax) (hρmax : ρmax < 1) :
    ∀ c1 : ℝ, 0 < c1 → ∃ D1 D2 D3 : ℝ, 0 < D1 ∧ 0 < D2 ∧ 0 < D3 ∧
      ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (PX : Measure (E d)) (η : E d → ℝ), IsDistr (PX, η) →
      ∀ cls : Set (Set (E d)), (∀ G ∈ cls, MeasurableSet G) →
      ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ ρmax → HasComplexityBound PX cls ρ A → bayesSet η ∈ cls →
      ∀ x : ℝ, D3 ≤ x →
      sampleLaw PX η n {s | x ≤ Vsup c1 ρ PX η cls s}
        ≤ ENNReal.ofReal (D1 * Real.exp (-D2 * x)) := by sorry

end ClassifAgg.Aggregation
