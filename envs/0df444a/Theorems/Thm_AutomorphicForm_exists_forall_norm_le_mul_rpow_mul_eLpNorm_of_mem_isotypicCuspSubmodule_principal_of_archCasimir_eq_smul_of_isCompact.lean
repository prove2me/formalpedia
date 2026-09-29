-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
-- name    : AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/30f99d38-fbb8-5703-ae55-96f78293a634
-- title:
--   Polynomial sup-norm bound on compacta for Casimir-eigen cusp forms
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $\xi_K$ be a homomorphism from the full subgroup of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ that is continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$, let $S_K$ be a finite set of finite places of $K$, let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ assign to each infinite place $w$ finitely many representations of the row-isometry subgroup at $w$, and let $C\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be compact. Then there exist $C_{\mathrm{st}},A\ge 0$, depending only on these data, with the following property. Let $\pi$ be a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with families $a_v,b_v\in\mathbb{C}$ indexed by the finite places) and let $\Lambda\ge 1$. Write $V$ for the intersection of two subspaces of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$: the $\mathbb{C}$-span of those $\varphi$ which are smooth cuspidal automorphic for the production pins built from the canonical truncation domain of $(\alpha,\beta)$, the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, the full central subgroup with character $\xi_K$, the level subgroups $M\mapsto \mathrm{principalLevel}(M)\sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}\,v$ and the conditional measure on the adele ring attached to the adelic box, and which in addition are continuous, right invariant under the level subgroup at $N$, Hecke coset eigenfunctions with eigenvalue $a_v$ at each $v\notin S_K$, and satisfy $\varphi(z(\det \mathrm{heckeGen}\,v)\,g)=b_v\varphi(g)$ for $v\notin S_K$; and the archimedean cut subspace, the infimum over infinite places $w$ of the supremum over the finitely many representations attached to $w$ of the corresponding type subspaces. Assume that for every real place $w$ there is $\lambda$ with $\|\lambda\|\le\Lambda$ such that every $b\in V$ is archimedean-smooth at $w$ and satisfies $\mathrm{archCasimirAt}\,b=\lambda b$, and that for every complex place $w$ there are $\lambda,\lambda'$ with $\|\lambda\|,\|\lambda'\|\le\Lambda$ such that every $b\in V$ is archimedean-smooth at $w$ in the complex sense and satisfies $\mathrm{archCasimirAtComplex}\,b=\lambda b$ and $\mathrm{archCasimirBarAtComplex}\,b=\lambda' b$. Then for every $b\in V$ and every $x\in C$, $\|b(x)\|\le C_{\mathrm{st}}\,\Lambda^{A}\,\|b\|_{L^2}$, where the last factor is the real number attached to the $L^2$ norm of $b$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to the canonical truncation domain of $(\alpha,\beta)$.
--
--   This is the locally uniform polynomial sup-norm estimate for cusp forms of fixed principal level and fixed archimedean types, with the $L^2$ norm taken over the truncation domain and the growth measured by the Casimir eigenvalues, obtained from the local Sobolev (kernel) estimate at the infinite places together with the comparison of $L^2$ norms over a compact set and over the truncation domain. It feeds the convergence statements for the cuspidal kernel $\sum_i b_i(x)\overline{b_i(y)}$ over an orthonormal family in the isotypic cusp space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
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

theorem AutomorphicForm.exists_forall_norm_le_mul_rpow_mul_eLpNorm_of_mem_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul_of_isCompact
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
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    ∃ Cst A : ℝ, 0 ≤ Cst ∧ 0 ≤ A ∧
      ∀ (π : HeckeEigensystem K ℂ) (Λ : ℝ), 1 ≤ Λ →
        (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧
          ∀ b ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAt hw b ∧ archCasimirAt hw b = lam • b) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
          ∀ b ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAtComplex hw b ∧ archCasimirAtComplex hw b = lam • b ∧
              archCasimirBarAtComplex hw b = lam' • b) →
        ∀ b ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
              (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
          ∀ x ∈ C,
            ‖b x‖ ≤ Cst * Λ ^ A *
              (eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal := by sorry
