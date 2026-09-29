-- Prove2me | Theorems.Thm_AutomorphicForm_paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite
-- name    : AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/eaabba82-d606-50b2-a3cc-0dbd85c8ea52
-- title:
--   Right convolution transports a Paley–Wiener slab profile datum
-- statement:
--   Let $K$ be a number field, let $0<\alpha<\beta$ be reals, let $SK$ be a finite set of finite places of $K$, and let $\xi_K$ be a homomorphism from the full group of idele units to $\mathbb{C}^\times$ that is continuous, trivial on the image of $K^\times$ and of absolute value $1$ at every point; let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $SK$, and let $tysK$ be a family of archimedean types (for each infinite place a finite list of representations of the local row-isometry group). Write $\alpha_m$ for the character of the idele units induced by the module (distributive Haar character) of the adele ring, assumed everywhere positive. Given a finite index type $\iota_P$ and families $\mu_e,\nu_e$ of continuous unitary characters of the idele units that are trivial on principal ideles and satisfy $\mu_e\nu_e=\xi_K$ on the central subgroup of the production pins attached to the canonical truncation domain for $(\alpha,\beta)$, the principal level groups intersected with the finite-adelic subgroup, the Hecke generators and the adelic box (that subgroup being all of the idele units), together with functions $\psi_e(s,\cdot)$ on $\mathrm{GL}_2(\mathbb{A}_K)$ such that each $\psi_e(s,\cdot)$ is a section induced from the pair $(\mu_e\,\alpha_m^{s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)})$ (i.e. transforms by the product of these characters evaluated on the two diagonal entries under left translation by the adelic Borel subgroup), which are jointly continuous in $(s,g)$, entire in $s$, and satisfy, for every $n$, every $\sigma_0$ and every compact $C$, a bound $(1+|t|)^n\|\psi_e(\sigma'+it,g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$ and $g\in C$ with $m$ integrable and bounded above; and given $\psi$ a slab profile for $\xi_K$ on that central subgroup (measurable, invariant under left translation by unipotents and by global Borel points, transforming by $\xi_K$ under the central scalars, bounded on determinant-norm slabs, and vanishing outside an adelic height band) with $\psi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it,g)\,dt$ for every real $\sigma'$; and given $f$ continuous with compact support, factorizable as an archimedean smooth compactly supported factor times a locally constant compactly supported finite factor, bi-invariant under $\mathrm{principalLevel}(N)$ intersected with the finite-adelic subgroup, and bi-finite for $tysK$ in the sense that $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule and $f$ in its dual counterpart: then, for the right convolution operator $\mathrm{convOp}\,K\,f\,u(g)=\int u(gx)f(x)\,dx$, all of the following hold. Each $\mathrm{convOp}\,K\,f\,(\psi_e(s,\cdot))$ is again a section induced from the same pair of characters; the family is jointly continuous in $(s,g)$ and entire in $s$; each member is archimedean $K$-finite and $K_f$-smooth; for each $e$ and each infinite place $w$ there is a single finite-dimensional space of functions on the archimedean row-isometry subgroup at $w$ containing all the functions $k\mapsto \mathrm{convOp}\,K\,f\,(\psi_e(s,\cdot))(gk)$, uniformly in $s$ and $g$; the same uniform rapid-decay bounds on vertical strips hold for the convolved family; each member is right invariant under $\mathrm{principalLevel}(N)$ intersected with the finite-adelic subgroup and lies in the archimedean cut submodule for $tysK$; $\mathrm{convOp}\,K\,f\,\psi$ is a slab profile for $\xi_K$ with the same vertical-line representation $\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\mathrm{convOp}\,K\,f\,(\psi_e(\sigma'+it,\cdot))(g)\,dt$; and right convolution commutes with the formation of pseudo-Eisenstein series, $\mathrm{convOp}\,K\,f\,(\mathrm{pseudoEisenstein}\,K\,\psi)=\mathrm{pseudoEisenstein}\,K\,(\mathrm{convOp}\,K\,f\,\psi)$ pointwise.
--
--   This is the statement that the right regular action of a test function $f$ preserves the whole package of data attached to a Paley–Wiener family of induced sections and its associated pseudo-Eisenstein series, and that $R(f)$ commutes with the theta-series construction $\psi\mapsto\theta_\psi$. It supplies the hypothesis list on the section side for the Parseval-type identity pairing $\theta_\psi$ with $\theta_{R(f)\psi}$ along the unitary axis, where level-$N$ invariance and membership in the archimedean cut are what allow the flat orthonormal level-$N$ families to be used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP) (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    (∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (convOp K f (ψf e s))) ∧
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => convOp K f (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => convOp K f (ψf e s) g)) ∧
    (∀ e s, IsArchKFinite K (convOp K f (ψf e s))) ∧ (∀ e s, IsKfSmooth K (convOp K f (ψf e s))) ∧
    (∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k : ↥(archRowIsometrySubgroup K w) => convOp K f (ψf e s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
      ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
        ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (∀ e (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, convOp K f (ψf e s) (g * u) = convOp K f (ψf e s) g) ∧
    (∀ e (s : ℂ), convOp K f (ψf e s) ∈ archCutSubmodule K tysK) ∧
    AutomorphicForm.IsSlabProfile K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK (convOp K f ψ) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
      convOp K f ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
        ∫ t : ℝ, convOp K f (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K,
      convOp K f (AutomorphicForm.pseudoEisenstein K ψ) g = AutomorphicForm.pseudoEisenstein K (convOp K f ψ) g) := by sorry
