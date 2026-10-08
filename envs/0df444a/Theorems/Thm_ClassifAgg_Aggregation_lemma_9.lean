-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_9
-- name    : ClassifAgg.Aggregation.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:34.953422+00:00
-- url     : https://prove2.me/theorems/95b8ed5f-cc56-479d-8c44-27e357d53d7f
-- title:
--   Lemma 9, p. 164 — P(V_0n(𝒢) ≥ x n^{−1/(1+ρ)}) ≤ B₁ exp(−B₂ n^{ρ/(1+ρ)}) for all x ≥ B₃
-- statement:
--   Let $A>0$ and $0<\rho_{\min}<\rho_{\max}<1$, and let $c_2>0$. There exist $B_1>0$, $B_2>0$, $B_3>0$, depending only on $A,\rho_{\min},\rho_{\max}$ and $c_2$, with the following property.
--
--   Let $n\ge1$, let $\pi=(P_X,\eta)$ be a distribution of $(X,Y)$, let $\rho\in[\rho_{\min},\rho_{\max}]$, and let $\mathcal G$ be a class of Borel sets having complexity bound $\rho$ with constant $A$ for $d_\triangle$, with $G^*\in\mathcal G$. Then
--   $$P_{\pi,n}\big(V_{0n}(\mathcal G)\ge xn^{-1/(1+\rho)}\big)\le B_1\exp\big(-B_2n^{\rho/(1+\rho)}\big)\qquad\forall\,x\ge B_3,$$
--   where $V_{0n}(\mathcal G)=\sup\{|R_n(G^*)-R_n(G)+d(G,G^*)|:G\in\mathcal G,\ d_\triangle(G,G^*)\le c_2n^{-1/(1+\rho)}\}$.
--
--   It controls the empirical excess risk on the small $d_\triangle$-ball around $G^*$.
--
--   **Formalization Note** The page calls $c_2$ "an arbitrary positive constant" and states constants depending only on $A,\rho_{\min},\rho_{\max}$. They cannot be independent of $c_2$ (for $c_2n^{-1/(1+\rho)}\ge1$ the supremum runs over all of $\mathcal G$ and is of order $n^{-1/2}$), so the constants here may depend on $c_2$, which is what the proofs use ($c_2=c_1$ or $c_2=\max(2,c_1)$). The standing assumptions are hypotheses, and the probability is the outer measure of the event.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, Lemma 9, p. 164

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Suprema
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_9 (A ρmin ρmax : ℝ) (hA : 0 < A) (hρmin : 0 < ρmin) (hρ : ρmin < ρmax) (hρmax : ρmax < 1) :
    ∀ c2 : ℝ, 0 < c2 → ∃ B1 B2 B3 : ℝ, 0 < B1 ∧ 0 < B2 ∧ 0 < B3 ∧
      ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (PX : Measure (E d)) (η : E d → ℝ), IsDistr (PX, η) →
      ∀ cls : Set (Set (E d)), (∀ G ∈ cls, MeasurableSet G) →
      ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ ρmax → HasComplexityBound PX cls ρ A → bayesSet η ∈ cls →
      ∀ x : ℝ, B3 ≤ x →
      sampleLaw PX η n {s | x * (n : ℝ) ^ (-1 / (1 + ρ)) ≤ V0sup c2 ρ PX η cls s}
        ≤ ENNReal.ofReal (B1 * Real.exp (-B2 * (n : ℝ) ^ (ρ / (1 + ρ)))) := by sorry

end ClassifAgg.Aggregation
