-- Prove2me | Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
-- name    : AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/aee80ea7-da3c-541c-8472-b0f806f310e1
-- title:
--   Convolution preserves the type-cut isotypic cusp space
-- statement:
--   Let $K \subseteq L$ be number fields (an algebra structure on $L$ over $K$), let $c_L,u_L,d_{1L},d_{2L}$ be real numbers with $d_{1L}<d_{2L}$, $0<c_L$ and $0<d_{1L}$, and let $T_L$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_L)$. Write $\mathcal{D}=\bigcup_{x\in T_L}\{g x\}$ for the union of the right translates by $T_L$ of `centreCutSiegelSet`, the set of $g$ whose finite part is integral, whose archimedean components have local height at least $c_L$ at every infinite place, squared window coordinate at most $u_L^2$, and archimedean determinant norm in $[d_{1L},d_{2L}]$; assume `CoversModCentre`, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_L)$ there are $\gamma\in\mathrm{GL}_2(L)$ and an idele unit $z$ with $\gamma g\,z\in\mathcal{D}$. Form the production pins of $L$ over $\mathcal{D}$, with level groups $N\mapsto$ `levelOne` $N$ intersected with the kernel of the archimedean projection, Hecke generators `heckeGen` at the finite places, and the adelic box; its centre subgroup is all of $(\mathbb{A}_L)^\times$, and $\xi_L$ is a character of it with values in $\mathbb{C}^\times$. Let $N_K$ be an ideal of $\mathcal{O}_K$, let $S_K$, $S_L$ be finite sets of primes of $K$, resp. $L$, such that every prime of $L$ contracting into $S_K$ lies in $S_L$ and every prime of $K$ dividing $N_K$ lies in $S_K$. Let $\Psi$ be a Hecke eigensystem for $L$ over $\mathbb{C}$ (a nonzero level ideal together with two complex-valued functions $a,b$ on the primes of $L$; no further condition), let $\mathrm{tys}_L$ be an archimedean type family for $L$ (at each infinite place $w$ a number $\mathrm{card}\,w$ of archimedean representations $\mathrm{rep}\,w\,i$), and let $\varphi\colon\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ satisfy `IsUnitFactorizableAboveOfType` for $K\subseteq L$, the family $\mathrm{tys}_L$, the level group attached to $N_K\mathcal{O}_L$ intersected with the archimedean kernel, and $S_K$; that is, $\varphi$ is unit-factorizable above $K$ for these data and archimedean bi-finite of type $\mathrm{tys}_L$. The conclusion is that the submodule $V$, the intersection of `isotypicCuspSubmodule` for these pins, $\xi_L$, the ideal $N_K\mathcal{O}_L$, $S_L$ and $\Psi$ (the complex span of the functions satisfying `IsIsotypicCuspFormAt` for those data) with `archCutSubmodule` for $\mathrm{tys}_L$ (the intersection over infinite places $w$ of the sums of the archimedean type submodules at the $\mathrm{rep}\,w\,i$), is stable under the operator $u\mapsto$ `rightConv` $u\,\varphi$: for every $u\in V$, `convOp` $\varphi\,u$ again lies in $V$.
--
--   This is the adelic form of the classical statement that the convolution operators of the Hecke algebra act on the space of cusp forms with fixed level, central character, Hecke eigenvalues and archimedean types. It is used, together with finite-dimensionality of the isotypic type-cut space, in the construction of test data for the Rankin–Selberg integrals and in the statement that convolution operators on that space are realised by finitely many explicit terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

theorem AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L) (hcL : 0 < cL) (hd₁L : 0 < d₁L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ)
    (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsUnitFactorizableAboveOfType K L tysL
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL,
      convOp L φ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL := by sorry
