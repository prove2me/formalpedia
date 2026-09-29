-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_tsum_convOp_mul_conj_unipotentGL2_mul_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrable_tsum_convOp_mul_conj_unipotentGL2_mul_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/435dba97-9a18-5130-9092-53259a64f268
-- title:
--   Integrability of the cuspidal kernel along unipotent orbits
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ contained in the slab $\{g : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$ (the idele norm being the modulus of the distributive Haar character) and a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\Phi_K$ be a further arbitrary subset, $\xi$ a homomorphism from the full subgroup of idele units to $\mathbb{C}^\times$, $S$ a finite set of finite places, and $N$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S$; let `tys` be a family assigning to each infinite place a finite list of representations of the relevant row-isometry group. Fix a type $\iota$, functions $b_i$ on $\mathrm{GL}_2(\mathbb{A}_K)$ and Hecke eigensystems $\mathrm{cls}(i)$ such that, for the carrier data `productionPinsOf` built from $\Phi$, the level subgroups $M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen` and the adelic box: each $\mathrm{cls}(i)$ is a cusp class (level $N$, vanishing $a_v,b_v$ for $v\in S$, non-zero isotypic cusp submodule) and each $b_i$ lies in the isotypic cusp submodule for $\mathrm{cls}(i)$ intersected with the archimedean cut submodule `archCutSubmodule` for `tys`; the $b_i$ are orthonormal over $\Phi$ for `adelicGLHaar`, i.e. $\int_\Phi b_i \overline{b_i} = 1$ and $\int_\Phi b_i\overline{b_j} = 0$ for $i \ne j$; and for every cusp class $\pi$ the fibre $\{i : \mathrm{cls}(i)=\pi\}$ is finite and the $b_i$ over it span the corresponding cut isotypic submodule. Let $f$ be continuous with compact support, factorizable as an archimedean smooth compactly supported factor times a locally constant compactly supported finite factor, bi-invariant under $\mathrm{principalLevel}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, and archimedean bi-finite for `tys`. Then for all $x,y \in \mathrm{GL}_2(\mathbb{A}_K)$ the function $q \mapsto \sum_i (\mathrm{convOp}\,f\,b_i)(x)\,\overline{b_i\bigl(\begin{smallmatrix}1&q\\0&1\end{smallmatrix}\bigr)y)}$, where $\mathrm{convOp}\,f\,b_i(g) = \int b_i(gu) f(u)\,du$, is integrable on $\mathbb{A}_K$ for the measure component $\nu$ of the carrier data attached to $\Phi_K$, namely the conditioning of adelic additive Haar measure on the adelic box; this measure does not depend on the carrier set, so $\Phi_K$ is immaterial to the conclusion.
--
--   This is the integrability input for the constant term of the cuspidal kernel along the unipotent orbit through $y$: the orbit integral of $K^{\mathrm{cusp}}_f(x,\cdot)$ against the compactly supported conditional measure on the adele group. It is used in the additivity of the one-cusp truncation across the blocks of the integrated Eisenstein expansion, in [`AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation`](thm.html#AutomorphicForm.exists_forall_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_eq_mul_integral_sum_rightConv_mul_setIntegral_lambdaT_axis_continuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_tsum_convOp_mul_conj_unipotentGL2_mul_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.integrable_tsum_convOp_mul_conj_unipotentGL2_mul_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
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
    ∀ x y : AdelicGL2 (𝓞 K) K,
      Integrable (fun q : AdeleRing (𝓞 K) K =>
          ∑' i, convOp K f (b i) x * conj (b i (AutomorphicForm.unipotentGL2 q * y)))
        (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν := by sorry
