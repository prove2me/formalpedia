-- Prove2me | Theorems.Thm_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d98d71fe-61a0-50e0-9dac-b8df52c70050
-- title:
--   Projection of an automorphic L² function onto a cut Hecke block
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi$ be a subset of the determinant slab $\{g\in\mathrm{GL}_2(\mathbb{A}_K):\ \|\det g\|\in[\alpha,\beta]\}$ (the norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the module of the idele on the adeles) which is a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` on the slab, with respect to the restriction of the adelic Haar measure `adelicGLHaar` to the slab. Let $\xi$ be a homomorphism from the full subgroup of the idele units to $\mathbb{C}^\times$, let $S$ be a finite set of finite places, let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S$, and let `tys` assign to each infinite place $w$ a finite list of representations of `rowIsometrySubgroup₀` of $K_w$. Write $P$ for the carrier pins `productionPinsOf` attached to $\Phi$, to the level family $M\mapsto \mathrm{principalLevel}(M)\sqcap$ `finiteAdelicGL2Subgroup`, to the Hecke generators `heckeGen`, and to `adelicBox`. Let $\Psi'$ be a Hecke eigensystem over $\mathbb{C}$ of level $N$ with $a_w=b_w=0$ for all $w\in S$, and put $W_{\Psi'}$ for the intersection of the $\mathbb{C}$-span of the functions that are isotypic cusp forms at $P$ for $(\xi,N,S,\Psi')$ — smooth cuspidal automorphic at $P$, continuous, right invariant under the level subgroup at $N$, Hecke eigenfunctions with eigenvalue $a_v$ and central eigenvalue $b_v$ at every $v\notin S$ — with the archimedean cut `archCutSubmodule` of `tys`, the infimum over infinite places of the supremum of the type submodules listed by `tys`. Let $v:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, square-integrable for the Haar measure restricted to $\Phi$, left invariant under $\mathrm{GL}_2(K)$ and transforming by $\xi$ under the adelic central scalars. Call $f$ admissible when it is continuous, has compact support, satisfies $f(ug)=f(g)=f(gu)$ for $u$ in $\mathrm{principalLevel}(N)\sqcap$ `finiteAdelicGL2Subgroup`, and is archimedean bi-finite of type `tys`, that is $x\mapsto f(x^{-1})$ lies in the archimedean cut and $f$ in the archimedean dual cut. Assume that for every admissible $f$ the convolution $\mathrm{convOp}(f)v:g\mapsto\int v(gx)f(x)\,d\mu(x)$ lies in $W_{\Psi'}$. Then there is $u_1\in W_{\Psi'}$ such that $\mathrm{convOp}(f)v=\mathrm{convOp}(f)u_1$ for every admissible $f$, and such that $\int_\Phi v\,\overline{b}\,d\mu=\int_\Phi u_1\,\overline{b}\,d\mu$ for every Hecke eigensystem $\pi$ in `cuspClasses` at $P$ for $(\xi,N,S)$ — level $N$, vanishing $a$ and $b$ on $S$, nonzero isotypic submodule — and every $b$ in the intersection of the isotypic cusp submodule of $\pi$ with the archimedean cut.
--
--   This is the Hilbert-space step in the spectral decomposition of the cuspidal part: $u_1$ plays the role of the orthogonal projection of $v$ onto the finite-dimensional cut Hecke block $W_{\Psi'}$, so that $v-u_1$ is annihilated by every admissible convolution operator and is orthogonal, for the pairing $\int_\Phi a\overline{b}$, to every cut Hecke block. It feeds the statement that such a $v$ lies in the sum of the cut isotypic cuspidal blocks.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_mem_isotypicCuspSubmodule_inf_archCutSubmodule_forall_convOp_eq_and_setIntegral_mul_conj_eq_of_forall_convOp_mem_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ w : HeightOneSpectrum (𝓞 K), w.asIdeal ∣ N → w ∈ S)
    (tys : ArchTypeFamily K)
    (Ψ' : HeckeEigensystem K ℂ) (hΨ'N : Ψ'.level = N) (hΨ'S : ∀ w ∈ S, Ψ'.a w = 0 ∧ Ψ'.b w = 0)
    (v : AdelicGL2 (𝓞 K) K → ℂ) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v) (hvc : Continuous v)
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ))
    (hR : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
        IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
        IsArchBiFinite K tys f →
      convOp K f v ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys) :
    ∃ u₁ ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ' ⊓ archCutSubmodule K tys,
      (∀ (f : AdelicGL2 (𝓞 K) K → ℂ), Continuous f → HasCompactSupport f →
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
          IsArchBiFinite K tys f →
        convOp K f v = convOp K f u₁) ∧
      ∀ π ∈ cuspClasses K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      ∀ b ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys,
        ∫ x in Φ, v x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
          ∫ x in Φ, u₁ x * conj (b x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
