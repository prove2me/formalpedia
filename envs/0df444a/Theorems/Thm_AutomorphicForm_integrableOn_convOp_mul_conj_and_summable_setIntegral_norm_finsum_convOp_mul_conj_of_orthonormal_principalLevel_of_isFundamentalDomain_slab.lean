-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/4446332a-9305-5f72-982a-f13497570340
-- title:
--   Integrability and class-wise summability of the cuspidal diagonal kernel
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be contained in the determinant slab $\{g:\|\det g\|\in[\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the module of the multiplication action on the adeles, and let $\Phi$ be a fundamental domain for the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ with respect to the adelic Haar measure restricted to that slab. Let $\xi$ be a homomorphism from the full group of ideles to $\mathbb{C}^\times$, let $S$ be a finite set of finite places, and let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S$; let $\mathcal{T}$ be a family of archimedean types, i.e. finitely many representations of the row-isometry group at each infinite place. Fix the carrier data consisting of $\Phi$, the levels $M\mapsto K(M)\cap\mathrm{GL}_2(\mathbb{A}_K)_{\mathrm{fin}}$ (principal congruence subgroups intersected with the kernel of the archimedean projection), the Hecke generators $\mathrm{heckeGen}\,v$ and the adelic box. Let $\iota$ be a type, $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to$ Hecke eigensystems over $\mathbb{C}$, such that for each $i$: $\mathrm{cls}(i)$ is a cusp class for these data, $\xi$, $N$, $S$ (its level is $N$, its $a$- and $b$-eigenvalues vanish on $S$, and its isotypic cuspidal submodule — the $\mathbb{C}$-span of the isotypic cusp forms attached to it — is nonzero), and $b_i$ lies in that isotypic submodule intersected with the $\mathcal{T}$-cut submodule $\bigsqcap_w\bigvee_i$ of archimedean type submodules; moreover $\int_\Phi b_i\overline{b_i}=1$ and $\int_\Phi b_i\overline{b_j}=0$ for $i\neq j$, and for every cusp class $\pi$ the set $\{i:\mathrm{cls}(i)=\pi\}$ is finite and the $b_i$ with $\mathrm{cls}(i)=\pi$ span the $\mathcal{T}$-cut isotypic submodule of $\pi$. Let $f$ be continuous with compact support, factorizable (a product of a smooth compactly supported function of the archimedean matrix entries and a locally constant compactly supported function of the finite part), bi-invariant under $K(N)\cap\mathrm{GL}_2(\mathbb{A}_K)_{\mathrm{fin}}$, and archimedean bi-finite for $\mathcal{T}$ (that is, $g\mapsto f(g^{-1})$ lies in the $\mathcal{T}$-cut submodule and $f$ in the dual cut submodule). Then, writing $(R(f)u)(g)=\int u(gx)f(x)\,dx$, each function $x\mapsto (R(f)b_i)(x)\,\overline{b_i(x)}$ is integrable on $\Phi$, and the family indexed by all Hecke eigensystems $\pi$ over $\mathbb{C}$, $$\pi\mapsto\int_\Phi\Bigl\|\sum_{i:\,\mathrm{cls}(i)=\pi}(R(f)b_i)(x)\,\overline{b_i(x)}\Bigr\|\,dx,$$ the inner sum being a finitary sum over the subtype $\{i:\mathrm{cls}(i)=\pi\}$, is summable.
--
--   This is the absolute-convergence input for the cuspidal part of the adelic trace formula at principal level: it asserts that the diagonal terms of the kernel of $R(f)$ against an orthonormal system adapted to the cuspidal Hecke classes are integrable over the fundamental domain and that the resulting class-by-class contributions sum absolutely. It is used to produce uniform bounds for the diagonal kernel on compact sets and feeds the class-kernel estimate at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.integrableOn_convOp_mul_conj_and_summable_setIntegral_norm_finsum_convOp_mul_conj_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
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
    (∀ i, IntegrableOn (fun x => convOp K f (b i) x * conj (b i x)) Φ
        (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    Summable (fun π : HeckeEigensystem K ℂ =>
      ∫ x in Φ, ‖∑ᶠ i : {i // cls i = π}, convOp K f (b i) x * conj (b i x)‖
        ∂adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
