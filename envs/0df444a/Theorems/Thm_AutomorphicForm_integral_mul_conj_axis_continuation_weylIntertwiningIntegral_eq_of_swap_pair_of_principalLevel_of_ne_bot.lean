-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
-- name    : AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/57145615-26f3-5e39-b572-dc8d9393ccef
-- title:
--   Adjointness of the GL₂ intertwining operator on the unitary axis
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb{A}$, and let $N$ be a non-zero ideal of $\mathcal{O}_F$. Write $|\cdot| = \alpha_m$ for the character $\mathbb{A}^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}$, assumed everywhere positive. Let $\mu,\nu : \mathbb{A}^\times \to \mathbb{C}^\times$ be continuous characters with $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$ and trivial on the image of $F^\times$. Let $(\varphi_s)_{s \in \mathbb{C}}$ be a family of functions on $GL_2(\mathbb{A})$ such that each $\varphi_s$ transforms under left multiplication by upper triangular $b$ (lower-left entry zero) by the factor $\big(\mu\,|\cdot|^{s+1/2}\big)(b_{11}) \cdot \big(\nu\,|\cdot|^{-(s+1/2)}\big)(b_{22})$, is archimedean $K$-finite (at each infinite place $w$ the right translates by the row-isometry subgroup span a finite-dimensional space), is $K_f$-smooth (its stabiliser inside the kernel of the archimedean projection is open), and is right invariant under `principalLevel (𝓞 F) F N` intersected with that kernel; the family is jointly continuous in $(s,g)$, holomorphic in $s$ for each $g$, and satisfies a uniform archimedean $K$-type condition: for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing $k \mapsto \varphi_s(gk)$ for all $s$ and $g$. Let $(\psi_s)_s$ be a family of the same kind for the reversed pair, i.e. with $\mu,\nu$ interchanged. Assume given open preconnected sets $O_\varphi, O_\psi \subseteq \mathbb{C}$, each containing the imaginary axis $\{\operatorname{re} s = 0\}$ and the half-plane $\{\operatorname{re} s > 1/2\}$, and functions $E_\varphi, N_\varphi$ (resp. $E_\psi, N_\psi$) of $(s,g)$ which are analytic in $s$ on the respective set for each $g$, jointly continuous on $O \times GL_2(\mathbb{A})$, and which for $\operatorname{re} s > 1/2$ agree with $\varphi_s(g) + \sum_{\xi \in F} \varphi_s(w\, u(\xi)\, g)$ (where $w$ is the adelic Weyl element and $u(\xi)$ the unipotent matrix with upper-right entry $\xi$) and with the Weyl intertwining integral $\int_{\mathbb{A}} \varphi_s(w^{-1} u(x) g)\,dx$ for the adelic additive Haar measure, respectively for $\psi$. Put $v = \big(\mathrm{vol}(\text{adelic box})\big)$, the real volume of `adelicBox F` for that Haar measure. Then for every real $t$, writing $M_\varphi = v^{-1} N_\varphi$ and $M_\psi = v^{-1} N_\psi$, $$\int_{\mathbf{K}} \varphi_{it}(k)\,\overline{M_\psi(-it)(k)}\,dk = \int_{\mathbf{K}} M_\varphi(it)(k)\,\overline{\psi_{-it}(k)}\,dk,$$ the integrals being over the adelic maximal compact subgroup (finite part integral, archimedean components row isometries) with its Haar measure `maximalCompactHaar F`.
--
--   This is the adjointness of the $GL_2$ intertwining (scattering) operator with respect to the $\mathbf{K}$-pairing on the unitary axis: the adjoint of $M(it) : I(\mu,\nu,it) \to I(\nu,\mu,-it)$ is $M(-it)$ in the reversed direction, stated for families admissible along the analytic continuation at a fixed principal level. It feeds the inner-product computations used in the spectral analysis of pseudo-Eisenstein series, such as the identification of axis pairings with sums of matrix coefficients and the Paley–Wiener matching statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot.lean

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

theorem AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (_hN : N ≠ ⊥) :
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
      (_hφflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, φf s (g * u) = φf s g)
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst ν αm hαm s) (etaSnd μ αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
        ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ψf s (g * u) = ψf s g)
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
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      (t : ℝ),
    (∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nψ (-((t : ℂ) * Complex.I)) g) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F)) =
    ∫ k, (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) * conj (ψf (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
      ∂(AutomorphicForm.maximalCompactHaar F) := by sorry
