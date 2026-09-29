-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/904adb4e-d7c4-594e-abaf-f413846a1863
-- title:
--   Uniform L² bound over compacta by fundamental-domain mass
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A} =$ `AdeleRing (𝓞 K) K`, and let $\chi$ be a group homomorphism from the full subgroup $\top$ of the idele group $\mathbb{A}^\times$ to $\mathbb{C}^\times$ (no continuity or unitarity assumed). Let $C \subseteq \mathrm{GL}_2(\mathbb{A})$ be compact, let $\alpha, \beta$ be reals with $0 < \beta$ and $\alpha < \beta$, and let $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A})$ be a measure-theoretic fundamental domain, in the sense of `IsFundamentalDomain`, for the action by left translation of the image of $\mathrm{GL}_2(K)$ under the entrywise map `globalPoints` induced by $K \to \mathbb{A}$, with respect to the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A})$ (for the Borel structure `glBorel`) restricted to the slab $\{g : \mathrm{ideleNorm}_K(\det g) \in [\alpha,\beta]\}$, where $\mathrm{ideleNorm}_K$ is the real value of the distributive Haar character of $\mathbb{A}$ at an idele. Then there is a real number $N$ such that for every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfying $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ and $\varphi(z g) = \chi(z)\varphi(g)$ for all ideles $z$ embedded as central scalar matrices, one has $\int^-_{C} \|\varphi\|^2 \le \mathrm{ENNReal.ofReal}\,N \cdot \int^-_{\Phi_0} \|\varphi\|^2$, the lower Lebesgue integrals being taken against `adelicGLHaar` with values in $[0,\infty]$, so no finiteness is asserted. The constant $N$ depends only on $K$, $\chi$, $C$, $\alpha$, $\beta$ and $\Phi_0$, not on $\varphi$.
--
--   This is the analytic input from reduction theory for $\mathrm{GL}_2$ over a number field: a compact set in $\mathrm{GL}_2(\mathbb{A})$ is covered by finitely many translates, by rational points and by bounded central elements, of a fundamental domain for the determinant-norm slab, so square masses over compacta are dominated uniformly. It is used in the construction of the cuspidal spectrum, notably to show that right convolution operators restricted to the cuspidal subspace are compact, and in the associated uniform estimates for convolution differences.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicHaar AutomorphicForm MeasureTheory
open scoped ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ N : ℝ, ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        ∫⁻ y in C, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal N * ∫⁻ y in Φ₀, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
