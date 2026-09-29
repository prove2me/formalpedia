-- Prove2me | Theorems.Thm_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/beccc5ba-31b8-512a-b274-850fffbe49c4
-- title:
--   Cuspidal kernel: locally uniform bounds and class-wise integrability
-- statement:
--   Let $K$ be a number field, $G=\mathrm{GL}_2(\mathbb A_K)$ with its Borel structure and Haar measure `adelicGLHaar`, and let $0<\alpha<\beta$ be reals. Let $\Phi\subseteq G$ be contained in the determinant slab $\{g:\|\det g\|_{\mathbb A}\in[\alpha,\beta]\}$ and be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on the Haar measure restricted to that slab. Fix a homomorphism $\xi$ from the full subgroup of idele units to $\mathbb C^\times$, a finite set $S$ of finite places, an ideal $N$ all of whose prime divisors lie in $S$, and an archimedean type family `tys`; the carrier data are those of `productionPinsOf` with domain $\Phi$, levels $U(M)=\mathrm{principalLevel}(M)\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, and the adelic box conditioning the additive Haar measure. Let $\iota$ be a type, $b:\iota\to(G\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` be such that each $\mathrm{cls}\,i$ is a cuspidal class (its level is $N$, its $a$- and $b$-eigenvalues vanish on $S$, and its isotypic cuspidal submodule — the span of the continuous $U(N)$-right-invariant smooth cuspidal automorphic functions with central character $\xi$ which are Hecke eigenfunctions of eigenvalue $a_v$ and central eigenvalue $b_v$ at all $v\notin S$ — is nonzero), with $b\,i$ in that submodule intersected with `archCutSubmodule K tys`; assume $\int_\Phi b_i\overline{b_i}=1$, $\int_\Phi b_i\overline{b_j}=0$ for $i\neq j$, and that for every cuspidal class $\pi$ the fibre $\{i:\mathrm{cls}\,i=\pi\}$ is finite and $b$ spans that intersected submodule. Let $f:G\to\mathbb C$ be continuous with compact support, factorizable (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor), bi-invariant under $\mathrm{principalLevel}(N)\sqcap$ `finiteAdelicGL2Subgroup`, and bi-finite for `tys` (i.e. $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tys` and $f$ in `archDualCutSubmodule K tys`). Then, writing $(R(f)u)(x)=\int_G u(xg)f(g)\,dg$ for `convOp K f u`: for every compact $C\subseteq G$ there is $M\in\mathbb R$ such that for all $x,y\in C$ the family $i\mapsto\|(R(f)b_i)(x)\overline{b_i(y)}\|$ is summable with sum at most $M$; each $x\mapsto (R(f)b_i)(x)\overline{b_i(x)}$ is integrable on $\Phi$; and the function $\pi\mapsto\int_\Phi\bigl\|\sum_{\mathrm{cls}\,i=\pi}(R(f)b_i)(x)\overline{b_i(x)}\bigr\|\,dx$ is summable over all Hecke eigensystems $\pi$.
--
--   This is the convergence input for the cuspidal part of the kernel of $R(f)$ at a fixed level and fixed archimedean types: local uniform absolute convergence of the kernel on compacta, integrability of each diagonal term over the fundamental domain, and summability over cuspidal classes of the integrals of the class-wise diagonal kernels $K_\pi(x,x)=\sum_{\mathrm{cls}\,i=\pi}(R(f)b_i)(x)\overline{b_i(x)}$, which unlike the termwise integrals does not depend on the choice of orthonormal basis of each isotypic space. It is used in the statements that integrate the cuspidal kernel against truncation functions and against unipotent translates, on the way to the trace identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_FactorizableTestFn
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

theorem AutomorphicForm.forall_isCompact_exists_tsum_norm_convOp_mul_conj_le_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
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
    (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (hft : IsArchBiFinite K tys f) :
    (∀ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ∀ y ∈ C,
        Summable (fun i => ‖convOp K f (b i) x * conj (b i y)‖) ∧
        ∑' i, ‖convOp K f (b i) x * conj (b i y)‖ ≤ M) ∧
    (∀ i, IntegrableOn (fun x => convOp K f (b i) x * conj (b i x)) Φ
        (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    Summable (fun π : HeckeEigensystem K ℂ =>
      ∫ x in Φ, ‖∑ᶠ i : {i // cls i = π}, convOp K f (b i) x * conj (b i x)‖
        ∂adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
