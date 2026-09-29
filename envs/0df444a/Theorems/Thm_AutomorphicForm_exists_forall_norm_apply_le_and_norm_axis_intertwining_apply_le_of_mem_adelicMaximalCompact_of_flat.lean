-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
-- name    : AutomorphicForm.exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/e1fb8c2f-ca0a-5ce9-b8e7-460fe952d32b
-- title:
--   Uniform sup bound on K for flat induced families
-- statement:
--   Let $K$ be a number field, $S_K$ a finite set of finite places, and $\xi_K$ a homomorphism from the full unit group of the adele ring of $K$ to $\mathbb{C}^\times$ that is continuous, trivial on the image of $K^\times$, and of modulus $\|z\|^{w}$ for a fixed real $w$, where $\|\cdot\|$ is the idele norm given by the module of `distribHaarChar`. Let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, and let $\mathrm{tys}_K$ be an archimedean type family, i.e. for each infinite place $v$ a number $\mathrm{card}(v)$ of finite-dimensional representations of the row-isometry subgroup at $v$. Write $\alpha$ for the idele norm viewed as a homomorphism into $\mathbb{R}^\times$, and equip the adele ring with its Borel structure. The assertion is the existence of a single constant $C>0$, depending only on these data, such that the following holds for all further data: positivity of $\alpha$; continuous unitary characters $\mu,\nu$ of the idele group ($|\mu(x)|=|\nu(x)|=1$) trivial on $K^\times$ with $\mu(z)\nu(z)\|z\|^{w}=\xi_K(z)$; real archimedean parameters $\tau_\mu,\tau_\nu$ describing the local characters of $\mu,\nu$ at the positive real elements of each completion as $\|\cdot\|^{\,i\tau}$; integers $m_\mu,m_\nu$ describing those local characters on the norm-one elements as $x\mapsto x^{m}$; and a family $\psi_s$ on $\mathrm{GL}_2$ of the adeles such that each $\psi_s$ is an induced section for the pair of characters $\mu\,\alpha^{s+1/2}$, $\nu\,\alpha^{-(s+1/2)}$ (so $\psi_s(bg)$ equals $\mu\alpha^{s+1/2}(b_{11})\,\nu\alpha^{-(s+1/2)}(b_{22})\,\psi_s(g)$ for upper triangular $b$), each $\psi_s$ is archimedean $K$-finite at every infinite place and smooth for the finite-adelic subgroup (the kernel of the archimedean projection), the family is jointly continuous in $(s,g)$ and holomorphic in $s$, at each infinite place all right translates lie in one fixed finite-dimensional space, the family is flat on the maximal compact subgroup $\mathbf{K}$ (those $k$ whose finite part is integral and whose archimedean components are row isometries), right invariant under the intersection of the principal level $N$ with the finite-adelic subgroup, contained in the type-cut submodule determined by $\mathrm{tys}_K$, and normalised by $\int_{\mathbf{K}}|\psi_0|^2\le 1$; finally a set $O_\psi\subseteq\mathbb{C}$ that is open, preconnected and contains both the imaginary axis and the half-plane $\operatorname{Re}s>1/2$, together with functions $E_\psi,N_\psi$ analytic in $s$ on a neighbourhood of $O_\psi$, continuous on $O_\psi$ times the group, and agreeing for $\operatorname{Re}s>1/2$ with $\psi_s(g)+\sum_{\xi\in K}\psi_s(w\,u(\xi)\,g)$ and with the Weyl intertwining integral of $\psi_s$ against the additive adelic Haar measure respectively. Then for every real $t$ and every $k\in\mathbf{K}$ one has $\|\psi_{it}(k)\|\le C$ and $\|\mathrm{vol}(\text{adelic box})^{-1}N_\psi(it,k)\|\le C$.
--
--   This is the uniform sup-norm bound over the standard maximal compact subgroup of $\mathrm{GL}_2$ of the adeles, both for a flat level-$N$ typed holomorphic family of induced sections on the unitary axis and for its normalised Weyl intertwining image; the constant is uniform in the pair of unitary idele class characters with fixed product twist $\xi_K$. It serves as the input to the uniform bound for the constant term of unitary Eisenstein series on $\mathrm{GL}_2$, the constant term being the sum of the section and the normalised intertwining term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
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

theorem AutomorphicForm.exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
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
    ∃ (C : ℝ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K →
      ‖ψf ((t : ℂ) * Complex.I) k‖ ≤ C ∧
        ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) k‖ ≤ C := by sorry
