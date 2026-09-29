-- Prove2me | Theorems.Thm_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
-- name    : AutomorphicForm.exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/61ad3fa1-3f34-509d-ba65-f825e59e9069
-- title:
--   Equivariant K-finite averaging for slab profiles
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb{A}$, and let $\alpha\colon \mathbb{A}^\times \to \mathbb{R}^\times$ be the character obtained from the module $\mathrm{distribHaarChar}(\mathbb{A})$ by viewing its nonnegative real values as units, assumed everywhere positive. Fix a set $\Phi$ of matrices in $GL_2(\mathbb{A})$; it enters only as the fundamental-domain field of `productionPinsOf`, whose central subgroup $Z$ is all of $\mathbb{A}^\times$, so the given $\xi\colon Z \to \mathbb{C}^\times$ is a character of the full idele group, assumed continuous, of absolute value $1$, and trivial on the principal ideles. Let $\varphi\colon GL_2(\mathbb{A}) \to \mathbb{C}$ satisfy `IsSlabProfile`: it is measurable, left invariant under adelic upper unipotent matrices and under global points of the upper triangular Borel over $F$, satisfies $\varphi(zg) = \xi(z)\varphi(g)$ for central scalars $z \in Z$, is bounded on each slab $\|\det g\| \in [d_1, d_2]$ with $d_1 > 0$, and vanishes outside a band $a \le \mathrm{adelicHeight}(g) \le b$ with $a > 0$. Let $D \subseteq \mathbb{A}^\times$ be a measurable fundamental domain for the principal ideles acting on $\mathbb{A}^\times$ with its Haar measure, and write $\rho_D$ for the product of the restriction of that Haar measure to $D$ twisted by the density $\|t\|^{-1}$ with the Haar measure of the compact group $\mathbf{K} =$ `adelicMaximalCompact F` (finite part integral, each archimedean component a row isometry). Finally let $n \in \mathbb{N}$, let $\mu_j$ ($j \in \mathrm{Fin}\,n$) be continuous characters of $\mathbb{A}^\times$ of absolute value $1$ trivial on $F^\times$, let $h_j\colon \mathbb{R} \to \mathbb{C}$ be continuous, and let $m_j\colon \mathbf{K} \to \mathbb{C}$ be continuous, right $\mathbf{K}$-finite (all right translates $k \mapsto m_j(kk_0)$ lie in one finite-dimensional subspace of $\mathbf{K} \to \mathbb{C}$) and invariant under right multiplication by elements of $\mathbf{K}$ lying in some neighbourhood of $1$ and in the kernel of the archimedean projection. Then there exist characters $\nu_j$ of $\mathbb{A}^\times$ and functions $u_j\colon \mathbf{K} \to \mathbb{C}$ such that each $\nu_j$ is continuous, of absolute value $1$ and trivial on $F^\times$, with $\mu_j(z)\nu_j(z) = \xi(z)$ for all $z \in Z$; each $u_j$ is continuous, right $\mathbf{K}$-finite and invariant under the same kind of small finite-part right translations; for every $b$ in $\mathbf{K}$ whose lower-left entry vanishes and every $k \in \mathbf{K}$ one has $u_j(bk) = \eta_j(b) u_j(k)$, where $\eta_j(b) = \mu_j(b_{00})\alpha(b_{00})^{1/2}\,\nu_j(b_{11})\alpha(b_{11})^{-1/2}$ (the values `etaFst` and `etaSnd` at $s = 0$); and the $L^2(\rho_D)$ norm of $(t,k) \mapsto \varphi(\mathrm{diag}(t,1)k) - \sum_j \mu_j(t)\,h_j(\log\|t\|)\,u_j(k)$ is at most that of $(t,k) \mapsto \varphi(\mathrm{diag}(t,1)k) - \sum_j \mu_j(t)\,h_j(\log\|t\|)\,m_j(k)$, where $\|\cdot\|$ denotes the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19).
--
--   This is the averaging step which replaces an arbitrary $K$-finite family $(m_j)$ by one transforming under the Borel part of the maximal compact by the characters $\eta_j$ attached to $(\mu_j, \nu_j)$ with $\mu_j\nu_j = \xi$, without increasing the $L^2$ distance from the slab profile $\varphi$ along the diagonal Iwasawa section. It feeds the construction of induced sections approximating $\varphi$ in [`AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile`](thm.html#AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_equivariant_kFinite_eLpNorm_sub_sum_mul_le_of_isSlabProfile
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (_hξt : ∀ z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z,
        (z : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F → ξ z = 1)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
      (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
      (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
      (n : ℕ)
      (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ : ∀ j, IsUnitaryChar (𝓞 F) F (μ j)) (_hμic : ∀ j, IsIdeleClassChar (𝓞 F) F (μ j))
      (_hμc : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ))
      (h : Fin n → ℝ → ℂ) (_hh : ∀ j, Continuous (h j))
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ) (_hmc : ∀ j, Continuous (m j))
      (_hmW : ∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W)
      (_hmsm : ∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k),
    ∃ (ν : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (u : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (ν j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (ν j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν j x : ℂˣ) : ℂ)) ∧
      (∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ j, Continuous (u j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => u j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u' : ↥(adelicMaximalCompact F)),
        (u' : AdelicGL2 (𝓞 F) F) ∈ V → (u' : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          u j (k * u') = u j k) ∧
      (∀ (j : Fin n) (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbK : b ∈ adelicMaximalCompact F)
        (k : ↥(adelicMaximalCompact F)),
        u j (⟨b, hbK⟩ * k) =
          ((etaFst (μ j) α hα 0 (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((etaSnd (ν j) α hα 0 (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ) *
            u j k) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) *
              u j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ≤
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by sorry
