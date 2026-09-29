-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
-- name    : AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/da4ef932-7eff-5022-bb0c-b078ed97303f
-- title:
--   Casimir-weighted Hilbert–Schmidt bound for level-N convolution on cusp forms
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $\xi_K$ be a homomorphism from the full unit group of the adele ring of $K$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$, let $S_K$ be a finite set of finite places, let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be an archimedean type family (at each infinite place $w$ a finite list of representations of the relevant row-isometry subgroup), and let $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ be continuous, compactly supported, factorizable (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor), and bi-invariant under $\mathrm{principalLevel}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$; let $s\ge 0$. Then there is a real $M$ with the following property. Let $\iota$ be any type, $b:\iota\to(\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C})$ and $\mathrm{cls}:\iota\to\mathrm{HeckeEigensystem}\ K\ \mathbb{C}$ be such that each $\mathrm{cls}\,i$ belongs to $\mathrm{cuspClasses}$ for the production pins built from the canonical truncation domain $D=\mathrm{canonicalTruncationDomain}\ K\ \alpha\ \beta$, the level subgroups $M\mapsto\mathrm{principalLevel}(M)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $\mathrm{heckeGen}\,v$ and the adelic box (that is: its level is $N$, its $a_v$ and $b_v$ vanish for $v\in S_K$, and its isotypic cusp submodule is nonzero), and each $b\,i$ lies in the intersection of the isotypic cusp submodule of $\mathrm{cls}\,i$ with the type-cut submodule $\mathrm{archCutSubmodule}\ K\ \mathrm{tys}_K$; assume the $b\,i$ are orthonormal for the pairing $\int_D u\,\overline{v}$ against the adelic Haar measure on $\mathrm{GL}_2$. Let $\lambda^{\mathbb{R}},\lambda^{\mathbb{C}},\lambda^{\mathbb{C}'}$ assign to each Hecke eigensystem $\pi$ and each infinite place $w$ a complex number, such that at real $w$ one has $\lambda^{\mathbb{C}}_\pi(w)=\lambda^{\mathbb{C}'}_\pi(w)=0$ and every element $b'$ of that same intersection for $\pi$ is archimedean-smooth at $w$ with $\Omega_w b'=\lambda^{\mathbb{R}}_\pi(w)\,b'$, and at complex $w$ one has $\lambda^{\mathbb{R}}_\pi(w)=0$ and every such $b'$ is smooth in the complex sense at $w$ with $\Omega_w b'=\lambda^{\mathbb{C}}_\pi(w)\,b'$ and $\bar\Omega_w b'=\lambda^{\mathbb{C}'}_\pi(w)\,b'$. Then for every finite $F\subseteq\iota$,
--   $$\sum_{\pi\in\mathrm{cls}(F)}\Big(1+\sum_{w\mid\infty}\big(\|\lambda^{\mathbb{R}}_\pi(w)\|+\|\lambda^{\mathbb{C}}_\pi(w)\|+\|\lambda^{\mathbb{C}'}_\pi(w)\|\big)\Big)^{s}\sqrt{\sum_{i\in F,\ \mathrm{cls}\,i=\pi}\big\|\,b_i*f\,\big\|_{L^2(D)}^{2}}\ \le\ M,$$
--   where $(b_i*f)(g)=\int b_i(gx)f(x)\,dx$ and the $L^2$ norm is the $2$-norm for the Haar measure restricted to $D$.
--
--   This is the Casimir-weighted rapid-decay estimate for the Hilbert–Schmidt norms of right convolution by a fixed level-$N$ test function, taken blockwise over the cuspidal Hecke classes with a uniform bound $M$ independent of the orthonormal system, of the index type and of the finite subset. It feeds the convergence statements for the cuspidal contribution used later, namely the bounds on $\sum_i \|(b_i*f)(g)\overline{(b_i*f)(g)}\|$ over compact sets and the associated summability over a fundamental-domain slab.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul.lean

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

theorem AutomorphicForm.exists_forall_sum_rpow_mul_sqrt_sum_eLpNorm_convOp_sq_le_of_orthonormal_isotypicCuspSubmodule_principal_of_archCasimir_eq_smul
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
    (hfU : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (s : ℝ) (hs : 0 ≤ s) :
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
      ∀ (lamR lamC lamC' : HeckeEigensystem K ℂ → InfinitePlace K → ℂ),
        (∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsReal),
          lamC π w = 0 ∧ lamC' π w = 0 ∧
          ∀ b' ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAt hw b' ∧ archCasimirAt hw b' = lamR π w • b') →
        (∀ (π : HeckeEigensystem K ℂ) (w : InfinitePlace K) (hw : w.IsComplex),
          lamR π w = 0 ∧
          ∀ b' ∈ isotypicCuspSubmodule K
              (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
                (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK,
            IsArchSmoothAtComplex hw b' ∧ archCasimirAtComplex hw b' = lamC π w • b' ∧
              archCasimirBarAtComplex hw b' = lamC' π w • b') →
        ∀ (F : Finset ι) [DecidableEq (HeckeEigensystem K ℂ)],
          ∑ π ∈ F.image cls,
            (1 + ∑ w : InfinitePlace K, (‖lamR π w‖ + ‖lamC π w‖ + ‖lamC' π w‖)) ^ s *
              Real.sqrt (∑ i ∈ F.filter (fun i => cls i = π),
                (eLpNorm (convOp K f (b i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
                (AutomorphicForm.canonicalTruncationDomain K α β))).toReal ^ 2) ≤ M := by sorry
