-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat
-- name    : AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0d671616-6fb7-5280-8339-11bf11ea11e3
-- title:
--   Self-adjointness of M(0) on flat sections, case μ=ν
-- statement:
--   Let $F$ be a number field, let $\mathbb{A}$ denote its adele ring, equipped with its Borel $\sigma$-algebra, and let $\alpha_m\colon\mathbb{A}^\times\to\mathbb{R}^\times$ be the unit-valued homomorphism obtained from the distributive Haar character of $\mathbb{A}$ via $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed pointwise positive. Let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ be equal characters, each of absolute value $1$ everywhere, trivial on the principal ideles $F^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\varphi,\psi\colon\mathbb{C}\to GL_2(\mathbb{A})\to\mathbb{C}$ be two families such that, for every $s$, the function $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi_s(g)$ for all $b$ with $b_{10}=0$, where $\eta_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$; the right translates of $\varphi_s$ under the row-isometry subgroup at each infinite place span a finite-dimensional space; the stabiliser of $\varphi_s$ in the kernel of the archimedean projection is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is differentiable for each $g$; for each infinite place $w$ there is a finite-dimensional space $W$ of functions on the row-isometry subgroup at $w$ containing $k\mapsto\varphi_s(gk)$ for all $s,g$; and $\varphi$ is flat, $\varphi_s(k)=\varphi_0(k)$ for every $k$ in the maximal compact subgroup $\mathbf{K}=\mathrm{adelicMaximalCompact}\,F$ (integral at the finite places, row-isometric at the infinite places); the same hypotheses for $\psi$. Let $O_\varphi\subseteq\mathbb{C}$ be open and preconnected, containing the line $\mathrm{Re}\,s=0$ and the half-plane $\mathrm{Re}\,s>1/2$, and let $E_\varphi,N_\varphi$ be functions of $(s,g)$, analytic in $s$ on $O_\varphi$ for each $g$, jointly continuous on $O_\varphi\times GL_2(\mathbb{A})$, which for $\mathrm{Re}\,s>1/2$ are given by the Eisenstein sum $E_\varphi(s,g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)g)$ and by the Weyl intertwining integral $N_\varphi(s,g)=\int_{\mathbb{A}}\varphi_s(w^{-1}u(x)g)\,dx$ against additive adelic Haar measure, $w$ being the adelic Weyl element and $u(x)$ the upper unipotent matrix; let $O_\psi,E_\psi,N_\psi$ satisfy the same conditions for $\psi$. Write $c=\mathrm{vol}(\mathrm{adelicBox}\,F)$ for the additive Haar volume of the adelic box. Then, with respect to the Haar measure on $\mathbf{K}$, $$\int_{\mathbf{K}}\varphi_0(k)\,\overline{c^{-1}N_\psi(0,k)}\,dk=\int_{\mathbf{K}}c^{-1}N_\varphi(0,k)\,\overline{\psi_0(k)}\,dk.$$
--
--   This is the symmetry (self-adjointness) of the normalised scattering operator $M(0)=c^{-1}N(0,\cdot)$ at the centre of the unitary axis, for the $\mathbf{K}$-pairing and in the diagonal case $\mu=\nu$, stated for flat sections. It is obtained from the diagonal Maass–Selberg relation on the axis by letting the truncation parameter tend to the centre, and is used in the statements that assemble truncated inner products of continued Eisenstein families and their dominated sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat.lean

import Definitions.Def_AutomorphicForm_InducedSection
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

theorem AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_zero_eq_of_eq_of_flat
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hμν : μ = ν)
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
      (_hφflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        ψf s (k : AdelicGL2 (𝓞 F) F) = ψf 0 (k : AdelicGL2 (𝓞 F) F))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g)),
    (∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ 0 g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)) =
    ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ 0 g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf 0 (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) := by sorry
