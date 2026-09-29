-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a76095fb-1a18-5372-ba2f-a94d21a14d02
-- title:
--   Orthogonality of isotypic cusp forms for distinct Hecke eigensystems
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the determinant slab $\{g : \lVert\det g\rVert \in [\alpha,\beta]\}$, where $\lVert\cdot\rVert$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of an idele for the additive Haar measure on $\mathbb{A}_K$; assume $\Phi$ is a fundamental domain, in Mathlib's sense, for the action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` on the Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a homomorphism from the full unit group of $\mathbb{A}_K$ to $\mathbb{C}^\times$, let $N$ be an ideal of $\mathcal{O}_K$, and let $S$ be a finite set of finite places containing every $w$ with $w \mid N$. Fix the carrier data `productionPinsOf` built from $\Phi$, the level groups $M \mapsto \mathrm{principalLevel}(M) \sqcap \ker(\mathrm{glArch})$, the Hecke generators `heckeGen v`, and the adelic box (the Borel structure and `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$, central subgroup $\top$, and additive Haar measure conditioned on the box). Let $\pi,\pi'$ be Hecke eigensystems over $\mathbb{C}$ (each a level ideal, nonzero, together with families $a_v, b_v$ of complex numbers indexed by the finite places) lying in `cuspClasses` for these data, that is: level equal to $N$, $a_v = b_v = 0$ for all $v \in S$, and nonzero isotypic cusp submodule. Assume $\pi \neq \pi'$. Let $a$ lie in `isotypicCuspSubmodule` for $\pi$ and $b$ in that for $\pi'$, i.e. in the complex span of those $\varphi$ which are continuous smooth cusp automorphic functions with central character $\xi$, right invariant under the level group at $N$, and, at every $v \notin S$, Hecke coset eigenfunctions for `heckeGen v` with eigenvalue $a_v$ and eigenfunctions of the central translation by $\det(\mathrm{heckeGen}\ v)$ with eigenvalue $b_v$. Then $\int_\Phi a(g)\overline{b(g)}\,dg = 0$ for the Haar measure `adelicGLHaar`.
--
--   This is the adelic orthogonality of cusp forms belonging to distinct systems of Hecke eigenvalues, taken with respect to the unweighted inner product over an exact fundamental domain inside a determinant slab and at principal congruence level. It feeds the construction of orthonormal families in the isotypic spaces and the estimates for convolution operators used in the spectral analysis of the cuspidal space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ComplexConjugate

theorem AutomorphicForm.setIntegral_mul_conj_eq_zero_of_mem_isotypicCuspSubmodule_principalLevel_of_ne_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hNS : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (π π' : HeckeEigensystem K ℂ)
    (hπ : π ∈ cuspClasses K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S)
    (hπ' : π' ∈ cuspClasses K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S)
    (hne : π ≠ π')
    (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : a ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π)
    (hb : b ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π') :
    ∫ g in Φ, a g * conj (b g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0 := by sorry
