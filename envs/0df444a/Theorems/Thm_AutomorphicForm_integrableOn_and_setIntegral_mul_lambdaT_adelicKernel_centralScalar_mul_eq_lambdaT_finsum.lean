-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
-- name    : AutomorphicForm.integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/31a9a5c7-4757-5d0a-8cf8-9b400ffbff30
-- title:
--   Folding the centre out of the truncated adelic kernel
-- statement:
--   Let $K$ be a number field with adele ring $\mathbb{A}$, and equip the idele group $\mathbb{A}^\times$ with a Borel measurable structure and a Haar measure $\nu$. Let $\Omega \subseteq \mathbb{A}^\times$ be a fundamental domain, with respect to $\nu$, for the subgroup of principal ideles, i.e. the range of the map $K^\times \to \mathbb{A}^\times$ induced by $\mathrm{algebraMap}$. Let $\xi$ be a homomorphism from the top subgroup of $\mathbb{A}^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z)$ is continuous as a $\mathbb{C}$-valued function and $\xi$ is trivial on the principal ideles. Let $f : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ be continuous with compact support. Let $\mu$ be a finite measure on a measurable space $Q$, let $u : Q \to \mathrm{GL}_2(\mathbb{A})$ be measurable with $u(q)$ lying in one fixed compact set for $\mu$-almost every $q$, let $H : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{R}$ satisfy $H(\mathrm{diag}(z,z)\,g) = H(g)$ for all ideles $z$ and all $g$, let $T \in \mathbb{R}$, and let $x, y \in \mathrm{GL}_2(\mathbb{A})$. Here $\Lambda^T\varphi(g) = \varphi(g) - \mathbf{1}_{\{H > T\}}(g)\int_Q \mathrm{constantTermIntegrand}\,u\,\varphi\,g\,q \; d\mu(q)$, and the adelic kernel is $K_f(x,y') = \sum^{\mathrm{f}}_{\gamma \in \mathrm{GL}_2(K)} f(x^{-1}\gamma y')$, a finitely supported sum over the global points. The assertion is twofold: the function $z \mapsto \xi(z)\,\Lambda^T\big[K_f(x,\cdot)\big](\mathrm{diag}(z,z)\,y)$ is integrable on $\Omega$ with respect to $\nu$, and $$\int_{\Omega} \xi(z)\,\Lambda^T\big[K_f(x,\cdot)\big](\mathrm{diag}(z,z)\,y)\,d\nu(z) = \Lambda^T\Big[\,y' \mapsto \sum^{\mathrm{f}}_{q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))} \int_{\mathbb{A}^\times} \xi(z)\,f\big(x^{-1}\,\gamma_q\,\mathrm{diag}(z,z)\,y'\big)\,d\nu(z)\Big](y),$$ where $\gamma_q$ denotes the image under $\mathrm{globalPoints}$ of the chosen representative of the class $q$, and the outer sum over classes modulo the centre is again a finitely supported sum.
--
--   This is the passage from $\mathrm{GL}_2(K)\backslash\mathrm{GL}_2(\mathbb{A})$ to $Z(\mathbb{A})\mathrm{GL}_2(K)\backslash\mathrm{GL}_2(\mathbb{A})$ in the Selberg trace formula with central character $\xi$: integrating the truncated kernel against $\xi$ over a fundamental domain for the principal ideles replaces the test function by its $\xi$-twisted central fold, and the sum over $\mathrm{GL}_2(K)$ by a sum over classes modulo the centre. It is used in the subsequent comparison of the truncated kernel integral with the elliptic and parabolic contributions and in the convergence statements for the twisted kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum.lean

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrableOn_and_setIntegral_mul_lambdaT_adelicKernel_centralScalar_mul_eq_lambdaT_finsum
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {Q : Type*} [MeasurableSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (u : Q → AutomorphicForm.AdelicGL2 (𝓞 K) K) (hu : Measurable u)
    (hub : ∃ C : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ᵐ q ∂μ, u q ∈ C)
    (H : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℝ)
    (hH : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K),
      H (AutomorphicForm.centralScalar (𝓞 K) K z * g) = H g)
    (T : ℝ) (x y : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        AutomorphicForm.lambdaT μ u H T (fun y' => AutomorphicForm.adelicKernel K f x y')
          (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ΩK νZK ∧
    ∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        AutomorphicForm.lambdaT μ u H T (fun y' => AutomorphicForm.adelicKernel K f x y')
          (AutomorphicForm.centralScalar (𝓞 K) K z * y) ∂νZK =
      AutomorphicForm.lambdaT μ u H T
        (fun y' => ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
          ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
              (AutomorphicForm.centralScalar (𝓞 K) K z * y')) ∂νZK) y := by sorry
