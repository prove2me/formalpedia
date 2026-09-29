-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- name    : AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/a14f5988-0083-5a11-a2f3-f944c5269bb1
-- title:
--   Rapid decay of isotypic cusp forms on a determinant slab
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Let $\xi_K$ be a homomorphism from the full subgroup of the ideles $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function on $(\mathbb{A}_K)^\times$ is continuous and which is trivial on the image of $K^\times$ under the map of unit groups induced by $K \to \mathbb{A}_K$. Let $S_K$ be a finite set of finite places of $K$, and $N$ an ideal of $\mathcal{O}_K$ every prime divisor of which lies in $S_K$. Let $\mathrm{tys}_K$ be an archimedean type family, assigning to each infinite place $w$ a number $\mathrm{card}\,w$ of archimedean types $\mathrm{rep}\,w\,i$ at $w$, and let $\pi$ be a Hecke eigensystem over $\mathbb{C}$ for $K$ (a nonzero level ideal together with eigenvalue functions $a,b$ on finite places). Finally let $b : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ lie in the intersection of two $\mathbb{C}$-submodules of the functions on $\mathrm{GL}_2(\mathbb{A}_K)$: first, the isotypic cusp submodule, i.e. the span of the functions $\varphi$ satisfying `IsIsotypicCuspFormAt` for the character $\xi_K$, level $N$, finite set $S_K$ and eigensystem $\pi$, relative to the carrier data `productionPinsOf` built from the canonical truncation domain of the window $(\alpha,\beta)$, the level subgroups $M \mapsto$ `principalLevel` $(M) \sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` at each finite place, and the adelic box (the measure data being the Borel structures and adelic Haar measures on $\mathrm{GL}_2(\mathbb{A}_K)$ and $\mathbb{A}_K$, the latter conditioned on the box, with central subgroup the full idele unit group); and second, the archimedean cut submodule of $\mathrm{tys}_K$, the intersection over infinite places $w$ of the supremum of the archimedean type submodules at $w$ attached to $\mathrm{rep}\,w\,i$ for $i < \mathrm{card}\,w$. Then for every natural number $k$ there is a real $C \ge 0$ such that for all $g \in \mathrm{GL}_2(\mathbb{A}_K)$ whose idele norm $\|\det g\|$ (the module of the distinguished Haar character of $\mathbb{A}_K$ at $\det g$) lies in the closed interval $[\alpha,\beta]$, one has $\|b(g)\| \le C \cdot H(g)^{-k}$, where $H(g)$ is the adelic height, the product of the archimedean height of the archimedean part of $g$ with the finite height of its finite part.
--
--   This is the rapid-decay (uniform moderate-to-rapid decrease) property of cusp forms: an isotypic cusp form of fixed level and fixed archimedean type decays faster than any power of the adelic height, uniformly on the slab where the idele norm of the determinant is confined to $[\alpha,\beta]$. The bound is what makes the Rankin–Selberg and Mellin-type integrals against cusp forms converge; it is used in the analytic continuation and vanishing statements for those integrals against the cusp basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_exists_forall_norm_le_mul_inv_adelicHeight_pow_of_mem_isotypicCuspSubmodule_principal_inf_archCutSubmodule
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
          (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
        ‖b g‖ ≤ C * (NumberField.AdelicHeight.adelicHeight K g)⁻¹ ^ k := by sorry
