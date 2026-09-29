-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile
-- name    : AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/565411b6-89e6-5789-b3bb-3133bfb94181
-- title:
--   Induced sections replace K-finite factors without increasing L² distance
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb A_F)^\times$ obtained from the module (distributive Haar) character with values in $\mathbb R^\times$, assumed everywhere positive. Fix a subset $\Phi$ of $GL_2(\mathbb A_F)$; the carrier data `productionPinsOf` built from $\Phi$, the level-one subgroups `levelOne`, the Hecke generators `heckeGen` and the box `adelicBox` has central subgroup $Z=\top$, so that a character $\xi$ of this $Z$ is a character of the full idele group; it is assumed continuous, of absolute value $1$, and trivial on principal ideles. Let $\varphi : GL_2(\mathbb A_F)\to\mathbb C$ satisfy `IsSlabProfile`: $\varphi$ is measurable, invariant under left multiplication by upper unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb A_F$, and by the global points of the Borel subgroup (matrices over $F$ with vanishing $(1,0)$ entry), transforms by $\xi$ under left multiplication by central scalars, is bounded on each determinant slab $\{\,\|\det g\|\in[d_1,d_2]\,\}$ with $d_1>0$, and vanishes off a band $\{a\le \mathrm{adelicHeight}\le b\}$ with $a>0$. Let $D$ be a measurable fundamental domain for the principal ideles acting on the idele group with its Haar measure. Let $n\in\mathbb N$ and, for $j<n$, let $\mu_j$ be a continuous character of the idele group with $|\mu_j|=1$ that is trivial on $F^\times$, let $h_j:\mathbb R\to\mathbb C$ be continuous, and let $m_j$ be a continuous function on the maximal compact subgroup $\mathbf K$ (those $k$ whose finite part lies in $GL_2(\widehat{\mathcal O_F})$ and whose component at each infinite place is a row isometry) such that all right translates $k\mapsto m_j(kk_0)$ lie in one finite-dimensional subspace of $\mathbf K\to\mathbb C$, and such that $m_j(ku)=m_j(k)$ for all $k$ and all $u\in\mathbf K$ lying in some fixed neighbourhood $V$ of $1$ in $GL_2(\mathbb A_F)$ and in the kernel of the archimedean projection. Then there exist characters $\nu_j$ of the idele group and functions $\varphi_{0,j}$ on $GL_2(\mathbb A_F)$ such that each $\nu_j$ is continuous, of absolute value $1$ and trivial on $F^\times$; $\mu_j\nu_j=\xi$ on $Z$; each $\varphi_{0,j}$ is an induced section for the pair $(\mu_j\alpha^{1/2},\nu_j\alpha^{-1/2})$, i.e. $\varphi_{0,j}(bg)=\mu_j\alpha^{1/2}(b_{00})\,\nu_j\alpha^{-1/2}(b_{11})\,\varphi_{0,j}(g)$ for all upper-triangular $b$ and all $g$; each $\varphi_{0,j}$ is archimedean $\mathbf K$-finite, $K_f$-smooth and continuous; and, with the measure $\|t\|^{-1}\,d^\times t|_D\otimes dk$ on $D\times\mathbf K$, the $L^2$-norm of $(t,k)\mapsto \varphi(\mathrm{diag}(t,1)k)-\sum_j \mu_j(t)h_j(\log\|t\|)\varphi_{0,j}(k)$ is at most that of $(t,k)\mapsto\varphi(\mathrm{diag}(t,1)k)-\sum_j\mu_j(t)h_j(\log\|t\|)m_j(k)$.
--
--   This is the averaging step over $B(\mathbb A_F)\cap\mathbf K$ in the treatment of slab profiles: an elementary sum with arbitrary $\mathbf K$-finite, $K_f$-smooth factors $m_j$ may be replaced, without loss in $L^2$ distance to the profile, by one whose $\mathbf K$-factors are restrictions of continuous sections of the induced representations attached to $(\mu_j\alpha^{1/2},\nu_j\alpha^{-1/2})$. It feeds the Paley–Wiener density statement for slab profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile.lean

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

theorem AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile
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
    ∃ (ν : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (φ₀ : Fin n → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (ν j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (ν j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν j x : ℂˣ) : ℂ)) ∧
      (∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ j, IsInducedSection (𝓞 F) F (etaFst (μ j) α hα 0) (etaSnd (ν j) α hα 0) (φ₀ j)) ∧
      (∀ j, IsArchKFinite F (φ₀ j)) ∧ (∀ j, IsKfSmooth F (φ₀ j)) ∧ (∀ j, Continuous (φ₀ j)) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) *
              φ₀ j (p.2 : AdelicGL2 (𝓞 F) F)) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ≤
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) := by sorry
