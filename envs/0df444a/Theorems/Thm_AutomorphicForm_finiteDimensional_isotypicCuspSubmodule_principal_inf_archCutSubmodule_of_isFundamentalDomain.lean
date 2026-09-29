-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain
-- name    : AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/334fa15e-535a-51a9-bf59-c7be9eab4e21
-- title:
--   Finite-dimensionality of isotypic cusp spaces at principal level
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $S\subseteq\mathrm{GL}_2(\mathbb A_F)$ be contained in the slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the module of the distributive Haar character of $\mathbb A_F$; assume $S$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_F)$ on the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb A_F)$ restricted to that slab. Take the carrier pins `productionPinsOf` attached to $F$ with domain $S$, level family $N\mapsto \mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $v\mapsto \mathrm{heckeGen}(v)$ and the adelic box (its central subgroup being all of $\mathbb A_F^{\times}$, its adelic measure the additive Haar measure conditioned on the box). Let $\xi$ be a character of that central subgroup with values in $\mathbb C^{\times}$, $N\neq 0$ an ideal of $\mathcal O_F$, $P$ a finite set of finite places, $\mathrm{tys}$ a family assigning to each infinite place $w$ a finite list of archimedean types, and $\Psi$ a Hecke eigensystem over $\mathbb C$. Then the $\mathbb C$-span of the functions $\varphi:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ that are smooth cuspidal automorphic for these pins and $\xi$, continuous, right invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, eigenfunctions of the Hecke coset operator of $\mathrm{heckeGen}(v)$ with eigenvalue $\Psi.a(v)$ for every $v\notin P$, and satisfying $\varphi(z(\det \mathrm{heckeGen}(v))g)=\Psi.b(v)\varphi(g)$ for $v\notin P$, intersected with the archimedean cut submodule $\bigcap_w\bigvee_i \mathrm{archTypeSubmoduleAt}(w,\mathrm{tys}.\mathrm{rep}\,w\,i)$, is a finite-dimensional $\mathbb C$-vector space.
--
--   This is the finiteness of a space of automorphic forms with prescribed level, central character, unramified Hecke eigenvalues and archimedean types, in the adelic $\mathrm{GL}_2$ setting and formulated relative to a fundamental domain of a determinant-norm slab. It feeds the construction of an orthonormal basis of such a space and the extraction of a single form with prescribed convolution and inner-product behaviour, and is the hypothesis-laden form from which the unconditional finiteness statement is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (S : Set (AdelicGL2 (𝓞 F) F))
    (hSs : S ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
        {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf F S
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (P : Finset (HeightOneSpectrum (𝓞 F)))
    (tys : ArchTypeFamily F) (Ψ : HeckeEigensystem F ℂ) :
    FiniteDimensional ℂ
      ↥(isotypicCuspSubmodule F
          (productionPinsOf F S
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N P Ψ
        ⊓ archCutSubmodule F tys) := by sorry
