-- Prove2me | Theorems.Thm_DiffVI_Exist_lemma_6_2
-- name    : DiffVI.Exist.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:26.98171+00:00
-- url     : https://prove2.me/theorems/610eccfa-f4c8-43df-b8eb-9e7c9a88a75f
-- title:
--   Lemma 6.2, p. 30 — under (6.5) the map 𝐅 of (6.4) has linear growth with ρ_f + ρσ_B(1 + ρ_G) and is upper semicontinuous on Ω
-- statement:
--   Let $K\subseteq\mathbb R^m$ be nonempty, closed and convex, and let $(f,B,G)$ satisfy (A) and (B) on $\Omega=[0,T]\times\mathbb R^n$, $T>0$. Let $\sigma_B$ bound $\|B(t,x)\|$ on $\Omega$, and let $\rho_f,\rho_G>0$ satisfy the linear growth (6.3): $\|f(t,x)\|\le\rho_f(1+\|x\|)$ and $\|G(t,x)\|\le\rho_G(1+\|x\|)$ on $\Omega$. Let $F:\mathbb R^m\to\mathbb R^m$ be continuous, suppose $\mathrm{SOL}(K,q+F)\neq\emptyset$ for all $q\in G(\Omega)$, and suppose there is $\rho>0$ with
--   $$\sup\{\|u\|: u\in\mathrm{SOL}(K,q+F)\}\le\rho(1+\|q\|)\qquad\forall q\in G(\Omega).\qquad(6.5)$$
--   Then the set-valued map $\mathbf F(t,x)=\{f(t,x)+B(t,x)u: u\in\mathrm{SOL}(K,G(t,x)+F)\}$ of (6.4) satisfies (6.1) with the constant
--   $$\rho_{\mathbf F}=\rho_f+\rho\,\sigma_B(1+\rho_G)>0,$$
--   that is, $\|y\|\le\rho_{\mathbf F}(1+\|x\|)$ for all $(t,x)\in\Omega$ and $y\in\mathbf F(t,x)$; and $\mathbf F$ is upper semicontinuous on $\Omega$.
--
--   Together with Lemma 6.1 this reduces existence for the DVI to the linear growth (6.5) of the static VI solutions and to convexity of their solution sets.
--
--   **Formalization Note** The page asserts that some $\rho_{\mathbf F}>0$ exists; the explicit value is the one in the paper's proof, so the Lean takes $\sigma_B,\rho_f,\rho_G$ as named constants with their bounds. "Closed-valued" follows from upper semicontinuity and is not restated.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 30, Lemma 6.2 and its proof, (6.3), (6.4), (6.5)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Lemma 6.2, p. 30: under (A), (B), continuity of `F`, nonemptiness of `SOL(K, q + F)` for
`q ∈ G(Ω)` and the linear growth (6.5) with constant `ρ`, the map `𝐅` of (6.4) satisfies (6.1)
with the constant `ρ_f + ρ σ_B (1 + ρ_G)` of the proof, and is upper semicontinuous on `Ω`. -/
theorem lemma_6_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : CondA T f B G)
    (σB : ℝ) (hσB : ∀ t ∈ Set.Icc 0 T, ∀ x, ‖B t x‖ ≤ σB)
    (ρf ρG : ℝ) (hρf : 0 < ρf) (hρG : 0 < ρG)
    (hf : ∀ t ∈ Set.Icc 0 T, ∀ x, ‖f t x‖ ≤ ρf * (1 + ‖x‖))
    (hG : ∀ t ∈ Set.Icc 0 T, ∀ x, ‖G t x‖ ≤ ρG * (1 + ‖x‖))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hFc : Continuous F)
    (hSOL : ∀ q ∈ GOmega T G, (SolodovSvaiterVI.Alg21.viSol (fun v => q + F v) K).Nonempty)
    (ρ : ℝ) (hρ : 0 < ρ) (hlin : LinGrowthSOL K G F T ρ) :
    (0 < ρf + ρ * σB * (1 + ρG) ∧
      ∀ t ∈ Set.Icc 0 T, ∀ x, ∀ y ∈ bigF K f B G F t x,
        ‖y‖ ≤ (ρf + ρ * σB * (1 + ρG)) * (1 + ‖x‖)) ∧
    IsUSCOnΩ T (bigF K f B G F) := by sorry

end DiffVI.Exist
