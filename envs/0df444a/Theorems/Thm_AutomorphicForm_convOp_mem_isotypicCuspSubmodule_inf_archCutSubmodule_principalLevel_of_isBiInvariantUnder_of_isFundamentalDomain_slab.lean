-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/29462c6c-b003-54e5-85b1-cc98c1e87ba9
-- title:
--   Right convolution preserves the cut isotypic cuspidal space
-- statement:
--   Let $K$ be a number field, $\alpha,\beta$ real with $0<\alpha$ and $\alpha<\beta$, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the determinant slab $\{g:\ \lVert\det g\rVert\in[\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), and which is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$, $S$ a finite set of finite places of $K$, $N$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S$, $\mathrm{tys}$ an archimedean type family (for each infinite place $w$ a finite list of representations of `rowIsometrySubgroup₀` of the completion at $w$), and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a,b$ of complex numbers indexed by the finite places). Write $\mathrm{pins}$ for the production pins `productionPinsOf` at $\Phi$ with the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, central subgroup $\top$, level family $M\mapsto U(M)=\,$`principalLevel`$(M)\sqcap$`finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, and the additive adelic Haar measure conditioned on `adelicBox`. Let $V$ be the $\mathbb{C}$-span of the functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying `IsIsotypicCuspFormAt` for these data, i.e. $\varphi$ satisfies `IsSmoothCuspAutomorphicFnAt K pins ξ`, is continuous, is right invariant under $U(N)$, and for every finite place $v\notin S$ satisfies `SmoothCusp.IsHeckeCosetEigenfunctionAt` for $U(N)$ and the generator `heckeGen v` with eigenvalue $\Psi.a\,v$ and $\varphi(\mathrm{centralScalar}(\det(\mathrm{heckeGen}\,v))\,g)=\Psi.\mathrm{toRawCentral}.b\,v\cdot\varphi(g)$ for all $g$; let $C$ be the archimedean cut submodule, the infimum over infinite places $w$ of the supremum of the type submodules attached to the representations $\mathrm{tys}.\mathrm{rep}\,w\,i$. Let $f$ be continuous with compact support, bi-invariant under $U(N)$ in the sense that $f(ug)=f(g)=f(gu)$ for all $u\in U(N)$ and all $g$, and archimedean bi-finite of type $\mathrm{tys}$, i.e. $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ lies in the archimedean dual cut submodule. Then for every $u\in V\sqcap C$ the right convolution $g\mapsto\int u(gx)f(x)\,dx$ again lies in $V\sqcap C$.
--
--   This is the stability of a cuspidal isotypic block, cut by a family of archimedean types, under the convolution operators by bi-invariant archimedean-finite test functions. It is the input to the computation of the cuspidal contribution of the trace formula block by block, where the trace of such an operator is evaluated against an orthonormal family in the block.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K) (Ψ : HeckeEigensystem K ℂ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hft : IsArchBiFinite K tys f) :
    ∀ u ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ ⊓ archCutSubmodule K tys,
      convOp K f u ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ ⊓ archCutSubmodule K tys := by sorry
