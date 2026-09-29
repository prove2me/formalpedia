-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
-- name    : AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0c7343b4-cccf-50cf-b9d0-408fbffda40f
-- title:
--   Right translation by unit determinant norm preserves fundamental-domain integrals
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $\alpha,\beta$ be real numbers. Write $G = \mathrm{GL}_2(\mathbb{A}_K)$ for the general linear group of $2\times 2$ matrices over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and let $\|x\| = \mathrm{ideleNorm}_K(x)$ denote the real number obtained from the value of the distributive Haar character of $\mathbb{A}_K$ at an idele $x$. Let $S = \{g \in G : \|\det g\| \in [\alpha,\beta]\}$ be the corresponding determinant slab. Let $\Phi \subseteq G$ satisfy: $\Phi \subseteq S$, and $\Phi$ is a fundamental domain, in Mathlib's sense, for the action of the image subgroup $\mathrm{globalPoints}(\mathrm{GL}_2(K)) \le G$ (the image of $\mathrm{GL}_2(K)$ under the map induced by $K \to \mathbb{A}_K$) on $G$ with respect to the Haar measure of $G$ restricted to $S$. Let $h \in G$ with $\|\det h\| = 1$, and let $F : G \to \mathbb{C}$ be invariant under left translation by global points, i.e. $F(\mathrm{globalPoints}(\gamma)\, g) = F(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ and $g \in G$. Then $\int_{\Phi} F(gh)\,dg = \int_{\Phi} F(g)\,dg$, the set integrals being taken against the unrestricted Haar measure of $G$. No integrability or measurability hypothesis on $F$ is imposed, and $\alpha \le \beta$ is not assumed.
--
--   This is the standard unfolding device: an integral of a left $\mathrm{GL}_2(K)$-invariant function over a fundamental domain inside a determinant slab is unchanged when the variable is translated on the right by an adelic element of trivial determinant norm, since such a translation preserves the slab and the Haar measure. It is used throughout the analysis of automorphic forms on $\mathrm{GL}_2(\mathbb{A}_K)$ in this development, for instance in the bounds on convolution operators and in the control of $K$-type averages.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_comp_mul_eq_setIntegral_of_isFundamentalDomain_of_ideleNorm_det_eq_one
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (h : AdelicGL2 (𝓞 K) K) (hh : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det h) = 1)
    (F : AdelicGL2 (𝓞 K) K → ℂ)
    (hF : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), F (globalPoints (𝓞 K) K γ * g) = F g) :
    ∫ g in Φ, F (g * h) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = ∫ g in Φ, F g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
