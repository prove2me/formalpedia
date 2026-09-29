-- Prove2me | Theorems.Thm_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
-- name    : AutomorphicForm.paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/03678448-f2d2-5076-995e-c8407733e397
-- title:
--   Compact kernel averaging preserves Paley–Wiener families of induced sections
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal O_K$ and $\mathcal T$ (`tysK`) a family of archimedean types, i.e. for each infinite place $w$ a finite list of finite-dimensional representations of the row-isometry group at $w$. Let $\alpha$ be the homomorphism from the ideles of $K$ to $\mathbb R^\times$ obtained from the distributive Haar character of the adele ring, assumed everywhere positive, the adele ring carrying its Borel structure and $\mathrm{GL}_2$ of the adeles the associated Borel structure. Let $\kappa$ be a continuous complex function on the adelic maximal compact subgroup $\mathbf K$ (those $k$ whose finite part is integral and whose component at each infinite place is a row isometry), and let $P$ be an operator on complex functions on $\mathrm{GL}_2(\mathbb A_K)$ such that $P\varphi(g)=\int_{\mathbf K}\kappa(k)\varphi(gk)\,dk$ for the Haar measure `maximalCompactHaar`, such that $P$ carries continuous $K_\infty$-finite functions to continuous $K_\infty$-finite functions which are right invariant under $\Gamma=$ `principalLevel (𝓞 K) K N` $\sqcap$ `finiteAdelicGL2Subgroup K` and lie in the cut submodule of $\mathcal T$, and such that $P(\varphi(\cdot\,k))(g)=P\varphi(gk)$ for every $k\in\mathbf K$ whose archimedean component at each real place has determinant $1$. Let $\iota$ be a finite index type, $\mu_e,\nu_e$ idele class characters with values in $\mathbb C^\times$ ($\nu_e$ assumed continuous), and $\psi_e(s)$ a family of functions on $\mathrm{GL}_2(\mathbb A_K)$ such that each $\psi_e(s)$ is an induced section for the pair $\bigl(\mu_e\alpha^{s+1/2},\ \nu_e\alpha^{-(s+1/2)}\bigr)$, that is $\psi_e(s)(bg)=\chi_1(b_{11})\chi_2(b_{22})\psi_e(s)(g)$ for $b$ in the adelic Borel subgroup; the family is jointly continuous in $(s,g)$, entire in $s$ for fixed $g$, $K_\infty$-finite, $K_f$-smooth (open stabiliser inside the finite-adelic subgroup under right translation), uniformly $K_w$-finite (for each $e$ and $w$ a finite-dimensional space of functions on the row-isometry subgroup at $w$ containing all restrictions $k\mapsto\psi_e(s)(gk)$), and satisfies Paley–Wiener decay: for every $e$, $n$, $\sigma_0$ and compact $C$ there is an integrable bounded $m$ with $(1+|t|)^n\|\psi_e(\sigma'+it)(g)\|\le m(t)$ for $|\sigma'|\le\sigma_0$ and $g\in C$. The conclusion is that the averaged family $P\psi_e(s)$ has all eight of these properties with the same characters — induced section, joint continuity, holomorphy in $s$, $K_\infty$-finiteness, $K_f$-smoothness, uniform $K_w$-finiteness and the same Paley–Wiener decay bound — and in addition each $P\psi_e(s)$ is right invariant under $\Gamma$ and belongs to the cut submodule of $\mathcal T$.
--
--   This is the stability of a Paley–Wiener family of induced sections under averaging against a continuous kernel on the adelic maximal compact subgroup, the device by which a prescribed level $N$ and a prescribed family of archimedean types are imposed on such a family without destroying the growth and holomorphy conditions. It is used in the construction of the corresponding pseudo-Eisenstein series and the residual projection at level $N$ and type $\mathcal T$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne.lean

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

theorem AutomorphicForm.paleyWiener_sections_levelTypeAverage_of_kernel_maximalCompact_detOne
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (κ : ↥(adelicMaximalCompact K) → ℂ) (_hκ : Continuous κ)
      (P : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ))
      (_hP : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
        P φ g = ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))
      (_hPrange : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        Continuous (P φ) ∧ IsArchKFinite K (P φ) ∧ (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, (P φ) (g * u) = (P φ) g) ∧ P φ ∈ archCutSubmodule K tysK)
      (_hPcomm : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (k : ↥(adelicMaximalCompact K)),
        (∀ w : InfinitePlace K, w.IsReal →
          ((archComponent K w (glArch (𝓞 K) K (k : AdelicGL2 (𝓞 K) K)) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion).det = 1) →
        ∀ g : AdelicGL2 (𝓞 K) K, P (fun x => φ (x * (k : AdelicGL2 (𝓞 K) K))) g = P φ (g * (k : AdelicGL2 (𝓞 K) K)))
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
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
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t),
    (∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (P (ψf e s))) ∧
    (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => P (ψf e p.1) p.2)) ∧
    (∀ e g, Differentiable ℂ (fun s => P (ψf e s) g)) ∧
    (∀ e s, IsArchKFinite K (P (ψf e s))) ∧
    (∀ e s, IsKfSmooth K (P (ψf e s))) ∧
    (∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => P (ψf e s) (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖P (ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I)) g‖ ≤ m t) ∧
    (∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, P (ψf i s) (g * u) = P (ψf i s) g) ∧
    (∀ i (s : ℂ), P (ψf i s) ∈ archCutSubmodule K tysK) := by sorry
