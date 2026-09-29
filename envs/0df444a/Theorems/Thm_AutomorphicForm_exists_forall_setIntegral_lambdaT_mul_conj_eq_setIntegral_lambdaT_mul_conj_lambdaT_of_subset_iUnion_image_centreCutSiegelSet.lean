-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_of_subset_iUnion_image_centreCutSiegelSet
-- name    : AutomorphicForm.exists_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_of_subset_iUnion_image_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/9049ac31-8d0c-5a65-b799-727105e9b4e7
-- title:
--   Self-adjointness of Arthur truncation on a Siegel-covered fundamental domain
-- statement:
--   Let $F$ be a number field, let $0 < \alpha < \beta$ be reals, and let $c, u, d_1, d_2$ be reals with $c > 0$. Let $T_c$ be a compact set of adelic points $\mathrm{GL}_2(\mathbb{A}_F)$ and let $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ satisfy: $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂`, i.e. of the set of $g$ whose finite component lies in `finiteIntegralGL2` and which satisfy, at every infinite place $w$, $c \le$ `localHeight` of the $w$-component (the norm of its determinant divided by its row-norm square), `xWindowSq` of that component $\le u^2$, and `archDetNorm` $w\,g \in [d_1,d_2]$; $\Phi_0$ lies in the determinant slab $\{g : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$, the idele norm being the module of the Haar character; and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the adelic group, for the adelic Haar measure `adelicGLHaar` restricted to that slab. Then there is $T_0 \in \mathbb{R}$ such that for all $T \ge T_0$ and all measurable $a, b : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ invariant under left multiplication by the global points of the Borel subgroup (matrices in $\mathrm{GL}_2(F)$ with vanishing lower-left entry), if both $\Lambda^T a \cdot \overline{b}$ and $\Lambda^T a \cdot \overline{\Lambda^T b}$ are integrable on $\Phi_0$, then $\int_{\Phi_0} \Lambda^T a \cdot \overline{b} = \int_{\Phi_0} \Lambda^T a \cdot \overline{\Lambda^T b}$. Here $\Lambda^T \varphi = \varphi - \mathbf{1}_{\{g\,:\,T < H(g)\}} \cdot \varphi_N$, with $H$ the adelic height (the product of the archimedean and finite heights) and $\varphi_N$ the constant term of $\varphi$ along the unipotent family $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ taken against the additive adelic Haar measure conditioned to the adelic box (a probability measure).
--
--   This is the self-adjointness (orthogonal-projection) property of Arthur's truncation operator $\Lambda^T$ for $\mathrm{GL}_2$ in the one-cusp setting, stated for a truncation domain covered by finitely many, indeed compactly many, right translates of a centre-cut Siegel set. It is used in the computation of the continuous-spectrum contribution to the twisted trace formula that supports the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_of_subset_iUnion_image_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.exists_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_of_subset_iUnion_image_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)) (hTc : IsCompact Tc)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 F) F).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ), Measurable a → Measurable b →
        (∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
          a (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup F, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 F) F,
          b (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = b g) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (b g))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) →
        ∫ g in Φ₀,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          = ∫ g in Φ₀,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g)
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
