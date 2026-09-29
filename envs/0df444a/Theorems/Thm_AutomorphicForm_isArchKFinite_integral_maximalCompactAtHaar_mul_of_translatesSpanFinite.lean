-- Prove2me | Theorems.Thm_AutomorphicForm_isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite
-- name    : AutomorphicForm.isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d3bbac7c-e9a1-5499-af2a-d14be3af3320
-- title:
--   Archimedean K-finiteness of kernel averages over K_∞
-- statement:
--   Let $K$ be a number field, and let $\mathcal{K} =$ `maximalCompactAt K ∅` be the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ (here $\mathrm{GL}_2$ of the adele ring of $\mathcal{O}_K$ in $K$) consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ satisfies `IsRowIsometry`, intersected with the kernels of the maps to $\mathrm{GL}_2$ of the completion at $v$ for every finite place $v$ (the infimum is over the complement of $\emptyset$, hence over all of the height-one spectrum of $\mathcal{O}_K$), so that members of $\mathcal{K}$ have trivial finite part. Let $\kappa : \mathcal{K} \to \mathbb{R}$ be continuous and assume there is a finite set $s$ of real-valued functions on $\mathcal{K}$ such that for every $a \in \mathcal{K}$ the left translate $k \mapsto \kappa(ak)$ lies in the $\mathbb{R}$-span of $s$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, the adelic $\mathrm{GL}_2$ carrying its Borel structure. Then the function $x \mapsto \int_{\mathcal{K}} \kappa(k) f(xk)\,dk$, the integral taken against `maximalCompactAtHaar K ∅`, the Haar measure on $\mathcal{K}$ normalised to give mass one to the whole group, satisfies `IsArchKFinite K`: for every infinite place $w$ of $K$ the predicate `RightTranslatesSpanFinite` holds for this function with respect to the subgroup `archRowIsometrySubgroup K w`, a finiteness condition on its right translates by that subgroup.
--
--   This is the $K$-finiteness of the averaging operator $P_\kappa f(x) = \int_{\mathcal{K}_\infty} \kappa(k) f(xk)\,dk$ attached to a kernel $\kappa$ whose left translates span a finite-dimensional space, the standard mechanism for producing $K$-finite vectors from arbitrary continuous functions on $\mathrm{GL}_2(\mathbb{A}_K)$. It supplies the $K$-finiteness clause of [`AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul`](thm.html#AutomorphicForm.mem_isotypicCuspSubmodule_and_isArchKFinite_and_setLIntegral_le_of_integral_maximalCompactAtHaar_mul), where such averages are used to approximate cusp forms within a fixed isotypic component.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.isArchKFinite_integral_maximalCompactAtHaar_mul_of_translatesSpanFinite
    (K : Type) [Field K] [NumberField K]
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ)
    (hκfin : ∃ s : Finset (↥(maximalCompactAt K ∅) → ℝ), ∀ a : ↥(maximalCompactAt K ∅),
      (fun k => κ (a * k)) ∈ Submodule.span ℝ (s : Set (↥(maximalCompactAt K ∅) → ℝ)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) :
    IsArchKFinite K (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) := by sorry
