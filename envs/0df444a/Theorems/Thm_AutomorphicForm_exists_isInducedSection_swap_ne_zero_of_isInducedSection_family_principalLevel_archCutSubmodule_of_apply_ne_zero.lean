-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero
-- name    : AutomorphicForm.exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/42596467-cd78-5559-80ee-de59281c48c3
-- title:
--   Non-zero swapped induced section on the unitary axis
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal O_K$ and $\mathrm{tysK}$ an archimedean type family for $K$ (a number $\mathrm{card}(w)$ of archimedean representations $\mathrm{rep}(w,i)$ at each infinite place $w$). Write $\alpha_m$ for the character of $(\mathbb A_K)^\times$ obtained from the distributive Haar character of the adele ring pushed into $\mathbb R^\times$, and assume $\alpha_m(x)>0$ for all $x$. Let $\mu,\nu:(\mathbb A_K)^\times\to\mathbb C^\times$ be characters that are unitary ($|\mu(x)|=|\nu(x)|=1$ everywhere), trivial on the principal ideles coming from $K^\times$, and continuous. Let $\varphi_f:\mathbb C\times \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be a family such that for every $s$ the function $\varphi_f(s,\cdot)$ satisfies the induced-section identity $\varphi(bg)=\chi_1(d_1(b))\chi_2(d_2(b))\varphi(g)$ for $b$ in the adelic Borel subgroup, with $\chi_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\chi_2=\nu\cdot\alpha_m^{-(s+1/2)}$; each member is archimedean-$K$-finite at every infinite place and smooth for the finite-adelic subgroup (the kernel of the archimedean projection); the family is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$; at each infinite place there is one finite-dimensional space of functions on the archimedean row-isometry subgroup containing all right translates $k\mapsto\varphi_f(s,gk)$, uniformly in $s$ and $g$; each member is right invariant under the intersection of the principal level subgroup of $N$ with the finite-adelic subgroup; each member lies in the archimedean cut submodule of $\mathrm{tysK}$ (the intersection over infinite places of the sums of the type submodules attached to $\mathrm{rep}(w,i)$); and $\varphi_f(it_0,g_0)\neq 0$ for some real $t_0$ and some $g_0$. Then there exist a real $t$ and a function $\varphi_0$ on $\mathrm{GL}_2(\mathbb A_K)$ which is an induced section for the swapped pair $(\nu\cdot\alpha_m^{\,it+1/2},\ \mu\cdot\alpha_m^{-(it+1/2)})$, continuous, archimedean-$K$-finite, right invariant under the same level subgroup, a member of the archimedean cut submodule of $\mathrm{tysK}$, and non-zero. The conclusion asks neither for smoothness under the finite-adelic subgroup nor for any holomorphy.
--
--   This is the non-vanishing statement for the Weyl intertwining operator on the unitary axis: applying the standard intertwiner to a non-trivial family of sections induced from $(\mu,\nu)$ produces an admissible non-zero section of the pair with $\mu$ and $\nu$ interchanged, at the same level and with archimedean types in the same family. It feeds the Paley–Wiener matching and the orthogonality computations for pseudo-Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_isInducedSection_swap_ne_zero_of_isInducedSection_family_principalLevel_archCutSubmodule_of_apply_ne_zero
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite K (φf s))
      (_hφff : ∀ s, IsKfSmooth K (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf s (g * u) = φf s g)
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule K tysK)
      (_hne : ∃ (t₀ : ℝ) (g₀ : AdelicGL2 (𝓞 K) K), φf ((t₀ : ℂ) * Complex.I) g₀ ≠ 0),
    ∃ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
      IsInducedSection (𝓞 K) K (etaFst ν αm hαm ((t : ℂ) * Complex.I)) (etaSnd μ αm hαm ((t : ℂ) * Complex.I)) φ₀ ∧
      Continuous φ₀ ∧ IsArchKFinite K φ₀ ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) ∧
      φ₀ ∈ archCutSubmodule K tysK ∧ φ₀ ≠ 0 := by sorry
