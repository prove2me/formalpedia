-- Prove2me | Theorems.Thm_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
-- name    : AutomorphicForm.exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/05751284-3bb0-5da5-9b4b-402a1910187f
-- title:
--   Admissible flat family with prescribed maximal-compact values
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places of $K$, and $\xi_K$ a homomorphism from the full idele group $(\mathbb{A}_K)^\times$ (presented as the top subgroup) to $\mathbb{C}^\times$ which is continuous and trivial on the principal ideles coming from $K^\times$; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, let $\mathrm{tys}_K$ be an archimedean type family (a number $\mathrm{card}(v)$ of representations of the row-isometry group at each infinite place $v$), and let $w\in\mathbb{R}$ be such that $|\xi_K(z)| = \mathrm{ideleNorm}(z)^w$ for all ideles $z$, where the idele norm is the module of the scaling action on the adeles. Write $\alpha$ for the module character $x\mapsto \mathrm{distribHaarChar}(\mathbb{A}_K)(x)$ viewed in $\mathbb{R}^\times$. For a pair of characters $\mu,\nu$ of $(\mathbb{A}_K)^\times$ and a family $\psi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, admissibility (the predicate `Adm`) asserts: $\mu$ and $\nu$ have values of absolute value $1$ and are trivial on principal ideles; both are continuous; $\mu(z)\nu(z)\,\mathrm{ideleNorm}(z)^w=\xi_K(z)$ for all $z$; for every $s$ the function $\psi_s$ is an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\,\nu\cdot\alpha^{-(s+1/2)})$, i.e. $\psi_s(bg)=\mu(b_{11})\alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\,\psi_s(g)$ for all $g$ and all $b$ in the Borel subgroup (lower-left entry zero); each $\psi_s$ is archimedean $K$-finite (at each infinite place the right translates under the row-isometry subgroup span a finite-dimensional space) and smooth for the finite adelic subgroup (the kernel of the archimedean projection stabilises it with open stabiliser); $(s,g)\mapsto\psi_s(g)$ is jointly continuous and holomorphic in $s$ for each $g$; at each infinite place $v$ there is a finite-dimensional $\mathbb{C}$-subspace $W$ of functions on the archimedean row-isometry subgroup containing $k\mapsto\psi_s(gk)$ for all $s,g$; $\psi_s(k)=\psi_0(k)$ for every $s$ and every $k$ in the maximal compact subgroup (integral finite part, row-isometric archimedean part); $\psi_s$ is right invariant under the intersection of the principal level subgroup of $N$ with the finite adelic subgroup; and $\psi_s$ lies in the archimedean cut submodule determined by $\mathrm{tys}_K$, the intersection over infinite places $v$ of the sum of the type submodules of the representations $\mathrm{tys}_K.\mathrm{rep}\,v\,i$. Two pairs $(\mu',\nu')$ and $(\mu,\nu)$ are in the same class when $\mu(b_{11})\nu(b_{22})=\mu'(b_{11})\nu'(b_{22})$ for every $g$ lying in both the Borel subgroup and the maximal compact subgroup. The assertion is: assuming $\alpha$ takes positive values, given an admissible triple $(\mu',\nu',\psi')$ and characters $\mu,\nu$ that are unitary, trivial on principal ideles, continuous, satisfy $\mu\nu\,\mathrm{ideleNorm}^w=\xi_K$, and lie in the same class as $(\mu',\nu')$, there exists $\varphi$ such that $(\mu,\nu,\varphi)$ is admissible and $\varphi_s(k)=\psi'_0(k)$ for every $s\in\mathbb{C}$ and every $k$ in the maximal compact subgroup.
--
--   This is the section-extension step for flat families of induced sections on $\mathrm{GL}_2$ over the adeles: the values on the maximal compact subgroup of one admissible family are transported to any pair of characters in the same class, the Iwasawa decomposition $G=B\mathbf{K}$ supplying the extension off $\mathbf{K}$. It is used by the statements producing a finite admissible spanning set, and a basis with an $L^2$ bound, for flat families of the given level and archimedean type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    let Adm : (∀ x, 0 < ((αm x : ℝˣ) : ℝ)) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        (ℂ → AdelicGL2 (𝓞 K) K → ℂ) → Prop := fun hαm μ ν ψf =>
      IsUnitaryChar (𝓞 K) K μ ∧ IsUnitaryChar (𝓞 K) K ν ∧
      IsIdeleClassChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s)) ∧
      (∀ s, IsArchKFinite K (ψf s)) ∧
      (∀ s, IsKfSmooth K (ψf s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => ψf s g)) ∧
      (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
      (∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g) ∧
      (∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
    let SameClass : ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) →
        ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) → Prop := fun μ' ν' μ ν =>
      ∀ (g : AdelicGL2 (𝓞 K) K) (hg : g ∈ adelicBorel (𝓞 K) K), g ∈ adelicMaximalCompact K →
        ((μ (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ) =
          ((μ' (borelDiagFst ⟨g, hg⟩) : ℂˣ) : ℂ) * ((ν' (borelDiagSnd ⟨g, hg⟩) : ℂˣ) : ℂ)
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ψf' : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hadm : Adm hαm μ' ν' ψf')
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hclass : SameClass μ' ν' μ ν),
    ∃ φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ, Adm hαm μ ν φ ∧
      ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = ψf' 0 (k : AdelicGL2 (𝓞 K) K) := by sorry
