-- Prove2me | Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
-- name    : AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/99394e98-5bf0-5af1-b871-be8cf99e48b6
-- title:
--   Derivative words of Casimir-eigen cusp forms bounded on a slab
-- statement:
--   Let $K$ be a number field and $0 < \alpha < \beta$ real numbers. Let $\xi_K$ be a homomorphism from the full group of ideles $(\mathbb{A}_K)^\times$ (taken as the top subgroup) to $\mathbb{C}^\times$, assumed continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$. Let $S_K$ be a finite set of finite places of $K$, and $N$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$; let $\mathcal{T}$ be an archimedean type family, assigning to each infinite place $w$ finitely many representations of the relevant maximal compact subgroup of $\mathrm{GL}_2(K_w)$, and let $\pi$ be a Hecke eigensystem with values in $\mathbb{C}$. Let $b : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ lie in the intersection of two submodules: first, `isotypicCuspSubmodule` for the carrier data with Haar measure `adelicGLHaar` on `glBorel`, fundamental domain the canonical truncation domain `canonicalTruncationDomain K α β`, centre the full idele unit group, level subgroups $M \mapsto$ `principalLevel` $(M)$ intersected with `finiteAdelicGL2Subgroup`, Hecke coset generators `heckeGen`, and the measure on $\mathbb{A}_K$ obtained by conditioning `adelicAddHaar` on `adelicBox`, taken with character $\xi_K$, level $N$, excluded set $S_K$ and eigensystem $\pi$ — that is, the $\mathbb{C}$-span of the continuous functions that are smooth cusp automorphic at these pins with central character $\xi_K$, right invariant under the level subgroup at $N$, and, at each $v \notin S_K$, Hecke coset eigenfunctions with eigenvalue $\pi.a\,v$ and central eigenfunctions with eigenvalue $\pi.b\,v$; second, `archCutSubmodule` for $\mathcal{T}$, the infimum over infinite places $w$ of the supremum over the listed types at $w$ of the corresponding type submodules. Assume in addition that at every real place $w$ the function $b$ is archimedean smooth (all translates are $C^\infty$ in the real $2\times 2$ matrix variable at $w$ on the locus of nonvanishing determinant) and satisfies `archCasimirAt` $b = \lambda b$ for some $\lambda \in \mathbb{C}$, and that at every complex place $w$ it is archimedean smooth in the complex sense and satisfies `archCasimirAtComplex` $b = \lambda b$ and `archCasimirBarAtComplex` $b = \lambda' b$ for some $\lambda, \lambda' \in \mathbb{C}$. Let $W$ send a list of letters — each letter being either a real place $w$ together with a direction $H$, $E$ or $F$, or a complex place $w$ together with one of the six directions $H, E, F, iH, iE, iF$ — to the composite of the corresponding invariant derivations `archDerivAt` and `archDerivAtComplex`, applied by a right fold, so that the last letter of the list acts first. Then for every such list $l$: the function $W\,l\,b$ is continuous, is archimedean smooth at every real place and at every complex place, and there exists $B \in \mathbb{R}$ with $\|(W\,l\,b)(g)\| \le B$ for all $g \in \mathrm{GL}_2(\mathbb{A}_K)$ whose idele norm of $\det g$ lies in $[\alpha, \beta]$.
--
--   This is the regularity and boundedness statement for $K_\infty$-finite, Casimir-eigen cusp forms in the Harish-Chandra theory: every word in the invariant archimedean derivations applied to such a form is again continuous, archimedean smooth, and bounded on a determinant slab. It is consumed by the $L^2$ elliptic estimates [`AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact`](thm.html#AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact) and [`AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K) (π : HeckeEigensystem K ℂ)
    (b : AdelicGL2 (𝓞 K) K → ℂ)
    (hb : b ∈ isotypicCuspSubmodule K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
    (hbR : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      IsArchSmoothAt hw b ∧ ∃ lam : ℂ, archCasimirAt hw b = lam • b)
    (hbC : ∀ (w : InfinitePlace K) (hw : w.IsComplex),
      IsArchSmoothAtComplex hw b ∧ ∃ lam lam' : ℂ,
        archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∀ l, Continuous (W l b) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) ∧
      ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l b g‖ ≤ B := by sorry
