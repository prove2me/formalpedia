-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
-- name    : AutomorphicForm.exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/45303ad9-e494-5264-b0e0-f4c14e2b561f
-- title:
--   Unfolding Borel-coset sums into Iwasawa coordinates
-- statement:
--   Let $K$ be a number field. There is a constant $c$ with $0 < c < \infty$ (as an element of $[0,\infty]$) such that both of the following hold. First, for every measurable $S_0 \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ stable under left multiplication by the image of $\mathrm{GL}_2(K)$ under `globalPoints` (in the strong form: $\gamma g \in S_0 \iff g \in S_0$), every $\Phi_0 \subseteq S_0$ which is a fundamental domain for the left action of that image on the Haar measure `adelicGLHaar` restricted to $S_0$, every $\mathrm{reps} \subseteq \mathrm{GL}_2(K)$ containing exactly one $\rho$ with $g\rho^{-1}$ in the subgroup $B(K)$ of matrices with vanishing $(1,0)$ entry, for each $g \in \mathrm{GL}_2(K)$, every additive fundamental domain $X$ for the principal adeles in $\mathbb{A}_K$, every pair $\Omega_1,\Omega_2$ of fundamental domains for the principal ideles in $\mathbb{A}_K^\times$, and every measurable $F : \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$ with $F(\beta g) = F(g)$ for $\beta \in B(K)$, one has $$\int_{\Phi_0} \sum_{\rho \in \mathrm{reps}} F(\rho x)\,dg = c \int_X \int_{\Omega_1} \int_{\Omega_2} \int_{\mathbf{K}} (\mathbf{1}_{S_0} F)\bigl(n(x)\,z(u)\,a(t)\,k\bigr)\,|t|^{-1}\,dk\,d^\times t\,d^\times u\,dx,$$ where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, $z(u)$ is the scalar matrix with entry $u$, $a(t) = \mathrm{diag}(t,1)$, $|t|$ is the idele norm `ideleNorm`, and $dk$ is the Haar measure of mass $1$ on the adelic maximal compact subgroup $\mathbf{K}$ of `adelicMaximalCompact K`. Second, with the same $c$, the same identity with $c$ replaced by $c.\mathrm{toReal}$ holds for measurable $F : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ that are $B(K)$-invariant on the left, under the additional hypothesis that $\int_{\Phi_0} \sum_\rho \|F(\rho x)\| \, dg \neq \infty$.
--
--   This is the standard unfolding of a sum over the cosets $B(K)\rho$ of the rational Borel subgroup against Iwasawa coordinates $n(x)z(u)a(t)k$ on $\mathrm{GL}_2(\mathbb{A}_K)$, in both the $[0,\infty]$-valued and the absolutely convergent complex-valued form with a single common normalising constant. It underlies the constant-term and pseudo-Eisenstein estimates of the project, and is cited in the twisted Bruhat decomposition computation and in the finiteness and comparison results for integrals over the canonical truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa.lean

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.exists_forall_setLIntegral_tsum_borelSubgroup_cosets_eq_mul_lintegral_iwasawa
    (K : Type) [Field K] [NumberField K] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        ∫⁻ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          c * ∫⁻ x in X, ∫⁻ u in Ω₁, ∫⁻ t in Ω₂, ∫⁻ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) ∧
    (∀ (S₀ : Set (AdelicGL2 (𝓞 K) K)), MeasurableSet S₀ →
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), globalPoints (𝓞 K) K γ * g ∈ S₀ ↔ g ∈ S₀) →
      ∀ (Φ₀ : Set (AdelicGL2 (𝓞 K) K)), Φ₀ ⊆ S₀ →
        IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict S₀) →
      ∀ (reps : Set (GL (Fin 2) K)),
        (∀ g : GL (Fin 2) K, ∃! ρ : GL (Fin 2) K, ρ ∈ reps ∧ g * ρ⁻¹ ∈ borelSubgroup K) →
      ∀ (X : Set (AdeleRing (𝓞 K) K)) (Ω₁ Ω₂ : Set (AdeleRing (𝓞 K) K)ˣ),
        IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) X (adelicAddHaar (𝓞 K) K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₁
          (NumberField.Idele.idelicHaar K) →
        IsFundamentalDomain (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range Ω₂
          (NumberField.Idele.idelicHaar K) →
      ∀ F : AdelicGL2 (𝓞 K) K → ℂ, Measurable F →
        (∀ β ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, F (globalPoints (𝓞 K) K β * g) = F g) →
        (∫⁻ x in Φ₀, ∑' ρ : reps, ‖F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x)‖ₑ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≠ ∞) →
        ∫ x in Φ₀, ∑' ρ : reps, F (globalPoints (𝓞 K) K (ρ : GL (Fin 2) K) * x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          (c.toReal : ℂ) * ∫ x in X, ∫ u in Ω₁, ∫ t in Ω₂, ∫ k,
                S₀.indicator F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t * (k : AdelicGL2 (𝓞 K) K)) *
                  (((NumberField.TateGlobal.ideleNorm K t)⁻¹ : ℝ) : ℂ)
              ∂(maximalCompactHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K)
            ∂(adelicAddHaar (𝓞 K) K)) := by sorry
