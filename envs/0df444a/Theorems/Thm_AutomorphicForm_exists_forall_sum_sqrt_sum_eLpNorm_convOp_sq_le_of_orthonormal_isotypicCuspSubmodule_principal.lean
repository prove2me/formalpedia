-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
-- name    : AutomorphicForm.exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/f6531cd0-21e6-5095-851c-c573633f7e2f
-- title:
--   Block-wise summability of Hilbert–Schmidt norms of R(f)
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $\xi_K$ be a homomorphism from the full group of ideles $(\mathbb{A}_K)^\times$ (as the top subgroup) to $\mathbb{C}^\times$ whose associated complex-valued function is continuous and which is trivial on the image of $K^\times$, let $S_K$ be a finite set of finite places of $K$ and $N$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, and let $\mathcal{T}$ be an archimedean type family, i.e. for each infinite place $w$ a number $\mathcal{T}.\mathrm{card}\,w$ of representations of the local row-isometry subgroup at $w$. Let $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, compactly supported, factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor) and bi-invariant under $U(N):=\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$, meaning $f(ug)=f(g)=f(gu)$ for $u\in U(N)$. Then there is a real $M$ with the following property. Take the carrier data `productionPinsOf` consisting of the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the domain $\Phi_0=$ `canonicalTruncationDomain K α β`, the central subgroup $\top$, the levels $M\mapsto U(M)$, the local Hecke elements `heckeGen`, and the adelic Haar measure conditioned on `adelicBox K`. For every index type $\iota$, every family $b\colon\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and every assignment $\mathrm{cls}\colon\iota\to$ Hecke eigensystems over $\mathbb{C}$ such that, for each $i$, $\mathrm{cls}(i)$ is a cusp class for these data with character $\xi_K$, level $N$ and set $S_K$ (that is, its level is $N$, its $a$- and $b$-coefficients vanish at the places of $S_K$, and its isotypic cusp submodule, the span of the continuous $U(N)$-right-invariant smooth cuspidal automorphic functions with Hecke eigenvalue $a_v$ and central eigenvalue $b_v$ outside $S_K$, is nonzero), and $b_i$ lies in that isotypic cusp submodule intersected with the type-cut submodule $\bigsqcap_w\bigsqcup_i$ `archTypeSubmoduleAt` determined by $\mathcal{T}$, and such that the $b_i$ are orthonormal for the pairing $\int_{\Phi_0}u\,\overline{v}$ against the Haar measure, and for every finite $F\subseteq\iota$, one has $$\sum_{\pi\in \mathrm{cls}(F)}\Big(\sum_{i\in F,\ \mathrm{cls}(i)=\pi}\big\|\,b_i * f\,\big\|_{L^2(\Phi_0)}^2\Big)^{1/2}\le M,$$ where $b_i*f$ is the right convolution $g\mapsto\int b_i(gx)f(x)\,dx$ and the $L^2$ norm is taken for the Haar measure restricted to $\Phi_0$.
--
--   This is the block-wise trace-class estimate for the convolution operator $R(f)$ acting on the cut cuspidal spectrum at principal level $N$: the Hilbert–Schmidt norms of $R(f)$ on the individual Hecke-isotypic blocks are summable over the cuspidal classes, uniformly in the orthonormal system chosen. It is the weight-zero core from which the refinement involving powers of the archimedean Casimir eigenvalues, [`AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul), is obtained by shifting Casimir factors onto the test function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped ComplexConjugate

theorem AutomorphicForm.exists_forall_sum_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn K f)
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f) :
    ∃ M : ℝ, ∀ (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ),
      (∀ i, cls i ∈ cuspClasses K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK ∧
        b i ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK) →
      (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b i g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 1) →
      (∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, b i g * conj (b j g)
          ∂adelicGLHaar (Fin 2) (𝓞 K) K = 0) →
      ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
        ∑ π ∈ F.image cls,
          Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
            (eLpNorm (convOp K f (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2) ≤ M := by sorry
