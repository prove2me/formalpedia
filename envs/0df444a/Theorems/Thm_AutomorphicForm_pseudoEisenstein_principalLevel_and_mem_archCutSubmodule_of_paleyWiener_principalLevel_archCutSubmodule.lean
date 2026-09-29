-- Prove2me | Theorems.Thm_AutomorphicForm_pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule
-- name    : AutomorphicForm.pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/e3b37372-a2d1-5d65-8643-254a770cb515
-- title:
--   Level and archimedean type of a pseudo-Eisenstein series
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, and let $\xi_K$ be a character of the full unit group of the adele ring $\mathbb{A}_K$ with values in $\mathbb{C}^\times$ which is continuous, trivial on the image of $K^\times$, and of absolute value $1$ everywhere. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$ and $\mathcal{T}$ an archimedean type family, i.e. for each infinite place $w$ a finite list of finite-dimensional representations of the row-isometry subgroup at $w$. Write $\alpha_m$ for the $\mathbb{R}^\times$-valued character obtained from the module character $\mathrm{distribHaarChar}$ of $\mathbb{A}_K$, assumed everywhere positive. Given a finite index type $\iota_P$; families $\mu^P,\nu^P:\iota_P\to \widehat{\mathbb{A}_K^\times}$ of unitary continuous characters trivial on $K^\times$ with $\mu^P_e\nu^P_e=\xi_K$ (the subgroup $Z$ of the principal-level production pins for the canonical truncation domain of $(\alpha,\beta)$, levels $U(M)=\mathrm{principalLevel}(M)\cap\ker(\mathrm{glArch})$, Hecke generators and the adelic box being all of $\mathbb{A}_K^\times$); an involutive swap $r_P$ exchanging $\mu^P_e$ and $\nu^P_e$; separation of distinct indices by a norm-one idele; and a family $\psi f$ with $\psi f(e,s)$ an induced section for the pair $(\mu^P_e\,\alpha_m^{s+1/2},\ \nu^P_e\,\alpha_m^{-(s+1/2)})$, jointly continuous in $(s,g)$, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, uniformly $K_\infty$-finite (at each infinite place all right translates of all $\psi f(e,s)$ lie in one fixed finite-dimensional space of functions on the row-isometry subgroup), and of rapid vertical decay uniformly on compacta. Let $\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a slab profile for $\xi_K$ (measurable, invariant under left translation by adelic unipotents and by rational Borel points, transforming by $\xi_K$ under the centre, bounded on determinant slabs, supported in a height band) which on every vertical line satisfies $\psi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\psi f(e,\sigma'+it)(g)\,dt$. Assume finally that each $\psi f(e,s)$ is right invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ and lies in the archimedean cut submodule of $\mathcal{T}$, the intersection over infinite places $w$ of the sum of the type submodules of the representations $\mathcal{T}$ assigns to $w$. Then the pseudo-Eisenstein series $g\mapsto \psi(g)+\sum_{\beta\in K}\psi(w\,u(\beta)\,g)$ of $\psi$ is again right invariant under $\mathrm{principalLevel}(N)\cap\ker(\mathrm{glArch})$ and again lies in the archimedean cut submodule of $\mathcal{T}$.
--
--   The statement transports the two discrete invariants of a Paley–Wiener packet — the principal level $N$ and the prescribed archimedean $K$-types — from the induced sections, through the slab profile they represent, to the associated pseudo-Eisenstein series. It is used in the construction of matched Paley–Wiener pairs and in the comparison of pseudo-Eisenstein series with their residual projections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule.lean

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

theorem AutomorphicForm.pseudoEisenstein_principalLevel_and_mem_archCutSubmodule_of_paleyWiener_principalLevel_archCutSubmodule
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AutomorphicForm.pseudoEisenstein K ψ (g * u') = AutomorphicForm.pseudoEisenstein K ψ g) ∧
    AutomorphicForm.pseudoEisenstein K ψ ∈ archCutSubmodule K tysK := by sorry
