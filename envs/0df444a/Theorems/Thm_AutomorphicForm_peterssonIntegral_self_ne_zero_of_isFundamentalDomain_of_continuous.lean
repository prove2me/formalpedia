-- Prove2me | Theorems.Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
-- name    : AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/dd76b4e9-d776-5b7b-9d2d-2ba397142874
-- title:
--   Non-vanishing of the self-Petersson integral over a slab fundamental domain
-- statement:
--   Let $K$ be a number field, let $w, e_1, e_2$ be real numbers with $0 < e_1 < e_2$, and work in $\mathrm{GL}_2(\mathbb{A}_K)$, the group `AdelicGL2 (𝓞 K) K` of invertible $2\times 2$ matrices over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`; write $\lVert \det g\rVert$ for `ideleNorm`, the value at $\det g$ of the distributive Haar character of $\mathbb{A}_K$, viewed as a real number. Assume given a measurable set $\mathcal{F}$ contained in the closed slab $\{g : \lVert\det g\rVert \in [e_1,e_2]\}$ which is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action of the image of $\mathrm{GL}_2(K)$ under the entrywise map `globalPoints` induced by $K \to \mathbb{A}_K$, with respect to the Haar measure restricted to that slab. Assume further that $x : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ is continuous and satisfies $x(\gamma g) = x(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ (embedded via `globalPoints`) and all $g$, that there exists $g$ with $\lVert\det g\rVert$ in the open interval $(e_1,e_2)$ and $x(g) \neq 0$, and that $g \mapsto \lVert x(g)\rVert^2 \lVert\det g\rVert^{-w}$ is integrable on $\mathcal{F}$. Then the Petersson integral $\int_{\mathcal{F}} x(g)\,\overline{x(g)}\,\lVert\det g\rVert^{-w}\,dg$ is non-zero.
--
--   This is the positivity (non-degeneracy) statement for the diagonal of the weighted Petersson pairing on a slab fundamental domain: a continuous $\mathrm{GL}_2(K)$-invariant function not vanishing identically on the interior of the slab has non-zero self-pairing. It is used in the analysis of cuspidal constituents, where non-vanishing of the self-pairing of a test vector rules out degenerate cases in the Casimir eigenvalue computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_PeterssonIntegral
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
    (K : Type) [Field K] [NumberField K]
    (w e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂)
    (𝓕 : Set (AdelicGL2 (𝓞 K) K)) (h𝓕m : MeasurableSet 𝓕)
    (h𝓕s : 𝓕 ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂})
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 K) K).range 𝓕
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}))
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      x (globalPoints (𝓞 K) K γ * g) = x g)
    (hne : ∃ g : AdelicGL2 (𝓞 K) K,
      ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Ioo e₁ e₂ ∧ x g ≠ 0)
    (hint : IntegrableOn (fun g => ‖x g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕
      (adelicGLHaar (Fin 2) (𝓞 K) K)) :
    peterssonIntegral K w 𝓕 x x ≠ 0 := by sorry
