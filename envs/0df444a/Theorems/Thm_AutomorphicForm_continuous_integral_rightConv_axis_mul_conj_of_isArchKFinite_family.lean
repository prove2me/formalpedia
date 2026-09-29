-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family
-- name    : AutomorphicForm.continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/9025107e-e2c9-5f87-8c47-de65d1b91268
-- title:
--   Continuity in t of K-coefficients of πᵢₜ(f)
-- statement:
--   Let $F$ be a number field, $\mathbb{A}$ its adele ring, and let $\alpha_m$ denote the character $\mathbb{A}^\times \to \mathbb{R}^\times$ obtained from the module (`distribHaarChar`) of $\mathbb{A}$ viewed in $\mathbb{R}_{\ge 0}$, assumed everywhere strictly positive. Given two characters $\mu,\nu : \mathbb{A}^\times \to \mathbb{C}^\times$ that are unitary ($\|\mu(x)\|=\|\nu(x)\|=1$ for all $x$), trivial on the principal ideles $F^\times$, and continuous, and given two families $\varphi,\psi : \mathbb{C} \to GL_2(\mathbb{A}) \to \mathbb{C}$ such that for each $s$ the function $\varphi_s$ (resp. $\psi_s$) transforms under the adelic Borel subgroup by the pair of characters $\mu\cdot\alpha_m^{s+1/2}$, $\nu\cdot\alpha_m^{-(s+1/2)}$ evaluated on the two diagonal entries, is $K_\infty$-finite (at each infinite place $w$ its right translates under the image of the row-isometry subgroup of $GL_2(F_w)$ span a finite-dimensional space) and $K_f$-smooth, with $(s,g)\mapsto \varphi_s(g)$ jointly continuous, $s\mapsto\varphi_s(g)$ entire for each $g$, and a place-by-place uniform version of $K_\infty$-finiteness (one finite-dimensional space of functions on the row-isometry subgroup at $w$ containing all translates $k\mapsto\varphi_s(gk)$), and likewise for $\psi$; and let $f : GL_2(\mathbb{A})\to\mathbb{C}$ be continuous with compact support. Then $$t \longmapsto \int_{\mathbf{K}} \Big(\int_{GL_2(\mathbb{A})} \psi_{it}(kg) f(g)\,dg\Big)\,\overline{\varphi_{it}(k)}\,dk$$ is continuous on $\mathbb{R}$, the inner integral being against the adelic Haar measure on $GL_2(\mathbb{A})$ and the outer one against the Haar measure of the maximal compact subgroup $\mathbf{K}$ of $GL_2(\mathbb{A})$ (integral finite parts, row-isometric archimedean components).
--
--   This is the continuity, in the spectral parameter $t$ along the unitary axis, of the $\mathbf{K}$-matrix coefficient $\langle \pi_{it}(f)\psi_{it}, \varphi_{it}\rangle_{\mathbf{K}}$ of a compactly supported test function acting on a family of induced sections. It supplies the joint measurability and continuity input for the continuous-spectrum terms of the spectral expansion, and is cited in the statements that move the truncation integral inside the spectral sum and that estimate the resulting tails.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.continuous_integral_rightConv_axis_mul_conj_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (f : AdelicGL2 (𝓞 F) F → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
    Continuous (fun t : ℝ => ∫ k, rightConv F (ψf ((t : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 F) F) *
        conj (φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) := by sorry
