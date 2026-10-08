-- Prove2me | Theorems.Thm_ClassifAgg_Aggregation_lemma_11
-- name    : ClassifAgg.Aggregation.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:28.710251+00:00
-- url     : https://prove2.me/theorems/69815c50-f04d-43c5-920f-62380b2d2b41
-- title:
--   Lemma 11, p. 164 — P(sup_G |R_n(G*) − R_n(G) + d(G, G*)| ≥ t) ≤ C₂ exp(−nt²/C₂) for 0 < t ≤ 1
-- statement:
--   Let $A>0$ and $0<\rho_{\min}<\rho_{\max}<1$. There exists $C_2>0$, depending only on $A,\rho_{\min},\rho_{\max}$, with the following property.
--
--   Let $n\ge1$, let $\pi=(P_X,\eta)$ be a distribution of $(X,Y)$, let $\rho\in[\rho_{\min},\rho_{\max}]$, and let $\mathcal G$ be a class of Borel sets having complexity bound $\rho$ with constant $A$ for $d_\triangle$, with $G^*\in\mathcal G$. Then
--   $$P_{\pi,n}\Big(\sup_{G\in\mathcal G}|R_n(G^*)-R_n(G)+d(G,G^*)|\ge t\Big)\le C_2\exp(-nt^2/C_2)\qquad\forall\,0<t\le1.$$
--
--   This is a uniform deviation inequality for the empirical excess risk over the whole class, of sub-Gaussian type.
--
--   **Formalization Note** The standing assumptions of the Appendix are hypotheses, the constant is chosen before everything else, and the probability is the outer measure of the event.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, Appendix, Lemma 11, p. 164

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Suprema
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

theorem lemma_11 (A ρmin ρmax : ℝ) (hA : 0 < A) (hρmin : 0 < ρmin) (hρ : ρmin < ρmax) (hρmax : ρmax < 1) :
    ∃ C2 : ℝ, 0 < C2 ∧
      ∀ {d : ℕ} (n : ℕ), 1 ≤ n → ∀ (PX : Measure (E d)) (η : E d → ℝ), IsDistr (PX, η) →
      ∀ cls : Set (Set (E d)), (∀ G ∈ cls, MeasurableSet G) →
      ∀ ρ : ℝ, ρmin ≤ ρ → ρ ≤ ρmax → HasComplexityBound PX cls ρ A → bayesSet η ∈ cls →
      ∀ t : ℝ, 0 < t → t ≤ 1 →
      sampleLaw PX η n {s | t ≤ devSup PX η cls s}
        ≤ ENNReal.ofReal (C2 * Real.exp (-(n : ℝ) * t ^ 2 / C2)) := by sorry

end ClassifAgg.Aggregation
