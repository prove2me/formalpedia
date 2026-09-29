-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
-- name    : AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/df5ded3d-7a7d-5463-bdeb-7cb2e7d023ce
-- title:
--   Iwasawa majorant bound on the truncated high-height region
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Then there is a constant $C\in[0,\infty]$ with $C\neq\infty$ such that the following holds for every real cutoff $T$, every measurable $F\colon GL_2(\mathbb{A}_K)\to[0,\infty]$ (the adelic points being taken for the adele ring of $\mathcal{O}_K$ in $K$, with its Borel structure) which is left invariant under the subgroup `rationalTorusUnipotent K`, the join of `rationalTorus K` and `adelicUnipotent K`, in the sense that $F(xg)=F(g)$ for all $x$ in that subgroup and all $g$, and every $G\colon\mathbb{R}\times \mathbf{K}\to[0,\infty]$ whose uncurried form is measurable, where $\mathbf{K}=$ `adelicMaximalCompact K` is the subgroup of those $g$ whose finite component lies in `finiteIntegralGL2` and whose archimedean component at each infinite place of $K$ is a row isometry: if $G$ majorises $F$ in Iwasawa coordinates, i.e.
--   $$F\bigl(\mathrm{scalar}(z)\cdot \mathrm{diag}(y,1)\cdot k\bigr)\le \mathrm{ofReal}\,\|y\|\cdot G(\|y\|,k)$$
--   for all ideles $z,y$ and all $k\in\mathbf{K}$, where $\|y\|$ denotes [`NumberField.TateGlobal.ideleNorm K y`](def/NumberField_TateGlobalZeta.html#L19), the module of $y$ given by the distributive Haar character of $\mathbb{A}_K$ at $y$, then, with $dg$ the Haar measure `adelicGLHaar` of $GL_2(\mathbb{A}_K)$ and $dk$ the Haar measure `maximalCompactHaar` of $\mathbf{K}$,
--   $$\int_{\Phi\cap\{g\;:\;T<H(g)\}} F(g)\,dg\le C\int_{\mathbf{K}}\int_{(0,\infty)} G(y,k)\,\mathrm{ofReal}(y^{-1})\,dy\,dk,$$
--   where $\Phi=$ `canonicalTruncationDomain K α β` is the set component of the canonical truncation data attached to $\alpha,\beta$, and $H=$ [`NumberField.AdelicHeight.adelicHeight K`](def/NumberField_AdelicHeight.html#L158) is the product of the archimedean and finite heights of the corresponding components of $g$.
--
--   This is the measure-theoretic half of an $L^2$-criterion on the cuspidal region: an integral of a left $T(K)N(\mathbb{A}_K)$-invariant function over the part of the canonical truncation domain where the adelic height exceeds a cutoff is dominated, uniformly in the cutoff, by a single integral of an Iwasawa-coordinate majorant against $dy/y\,dk$. It is used in the construction of square-integrable automorphic objects, being cited by [`AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener); the proof combines the unfolding of the truncated integral into idelic and compact coordinates with Tate-style fundamental domain and idele-norm integration results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.exists_forall_setLIntegral_canonicalTruncationDomain_inter_lt_adelicHeight_le_mul_lintegral_Ioi_of_le_ideleNorm_mul
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ (T : ℝ) (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞), Measurable F →
        (∀ x ∈ rationalTorusUnipotent K, ∀ g : AdelicGL2 (𝓞 K) K, F (x * g) = F g) →
        ∀ (G : ℝ → adelicMaximalCompact K → ℝ≥0∞), Measurable (Function.uncurry G) →
        (∀ (z y : (AdeleRing (𝓞 K) K)ˣ) (k : adelicMaximalCompact K),
          F (centralScalar (𝓞 K) K z * diagOne y * (k : AdelicGL2 (𝓞 K) K)) ≤
            ENNReal.ofReal (NumberField.TateGlobal.ideleNorm K y) *
              G (NumberField.TateGlobal.ideleNorm K y) k) →
        ∫⁻ g in AutomorphicForm.canonicalTruncationDomain K α β ∩
            {g | T < NumberField.AdelicHeight.adelicHeight K g}, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤
          C * ∫⁻ k, ∫⁻ y in Set.Ioi (0 : ℝ), G y k * ENNReal.ofReal y⁻¹
            ∂volume ∂(maximalCompactHaar K) := by sorry
