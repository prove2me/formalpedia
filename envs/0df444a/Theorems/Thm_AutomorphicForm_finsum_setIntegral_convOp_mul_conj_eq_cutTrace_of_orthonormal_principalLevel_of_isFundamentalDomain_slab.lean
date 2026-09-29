-- Prove2me | Theorems.Thm_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f9b86d4e-bfea-5856-ac60-1c838caecfc1
-- title:
--   Cuspidal class contribution equals its cut trace, principal level
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi,\Phi_0\subseteq\mathrm{GL}_2(\mathbb A_K)$ both be contained in the determinant slab $\{g:\ \|\det g\|\in[\alpha,\beta]\}$ (with $\|\cdot\|$ the idele norm given by the module of the adelic Haar measure) and each be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that slab. Fix a homomorphism $\xi$ from the full subgroup $\top$ of $\mathbb A_K^\times$ to $\mathbb C^\times$, a finite set $S$ of finite places, an ideal $N$ of $\mathcal O_K$ all of whose prime divisors lie in $S$, and an archimedean type family `tys`. All isotypic data are read off the carrier pins `productionPinsOf K Φ` built from $\Phi$, the level family $M\mapsto$ `principalLevel` $M$ intersected with the finite-adelic subgroup, the Hecke generators `heckeGen`, and the adelic box; so a Hecke eigensystem $\pi$ belongs to `cuspClasses` when it has level $N$, has $a_v=b_v=0$ for $v\in S$, and has non-zero isotypic cusp submodule. Let $\iota$ be a type, $b:\iota\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` be such that for each $i$ the eigensystem $\mathrm{cls}(i)$ is a cusp class and $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with the archimedean cut submodule `archCutSubmodule K tys`; assume $\int_\Phi b_i\overline{b_i}=1$ and $\int_\Phi b_i\overline{b_j}=0$ for $i\neq j$, and that for every cusp class $\pi$ the fibre $\{i:\mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb C$-span of the corresponding $b_i$ is exactly the cut isotypic space of $\pi$. Let $f$ be continuous with compact support, bi-invariant under `principalLevel` $N$ intersected with the finite-adelic subgroup, and archimedean bi-finite for `tys` (i.e. $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule). Then for every cusp class $\Psi$ the finite sum over $i$ with $\mathrm{cls}(i)=\Psi$ of $\int_{\Phi_0}(\mathrm{convOp}\,f\,b_i)(x)\,\overline{b_i(x)}\,dx$, where $(\mathrm{convOp}\,f\,u)(g)=\int u(gx)f(x)\,dx$, equals `cutTrace` of $f$ at $\Psi$, namely the trace of right convolution by $f$ on the isotypic cusp submodule of $\Psi$ intersected with the archimedean cut submodule (taken to be $0$ if that space is not stable under the operator). Note that the orthonormality hypotheses are imposed over $\Phi$ while the matrix coefficients are integrated over the possibly different fundamental domain $\Phi_0$.
--
--   This is the class-by-class identification of the cuspidal part of the spectral side of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over $K$ at principal level: the diagonal matrix coefficients of right convolution by $f$, summed over an adapted orthonormal system spanning the cut isotypic space of $\Psi$, compute the trace of that operator on the space. It feeds the assembly of the full spectral identity in [`AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace`](thm.html#AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_mul_tsum_convOp_mul_conj_eq_mul_tsum_cutTrace).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.finsum_setIntegral_convOp_mul_conj_eq_cutTrace_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (tys : ArchTypeFamily K)
    (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S ∧
      b i ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S (cls i) ⊓ archCutSubmodule K tys)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0)
    (hbs : ∀ π ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S π ⊓ archCutSubmodule K tys)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hft : IsArchBiFinite K tys f)
    (Ψ : HeckeEigensystem K ℂ)
    (hΨ : Ψ ∈ cuspClasses K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S) :
    ∑ᶠ i : {i // cls i = Ψ},
        ∫ x in Φ₀, convOp K f (b i) x * conj (b i x) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      cutTrace K
        (productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ tys f hf hfc := by sorry
