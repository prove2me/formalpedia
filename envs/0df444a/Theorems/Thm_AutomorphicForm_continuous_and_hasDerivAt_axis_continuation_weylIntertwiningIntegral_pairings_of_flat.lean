-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
-- name    : AutomorphicForm.continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/59fe0e9d-acaf-59fe-8098-3ac8aa6d1a43
-- title:
--   Regularity and Cauchy–Schwarz bounds for flat Maass–Selberg pairings
-- statement:
--   Let $F$ be a number field, and let $\alpha$ denote the modulus character $x \mapsto \mathrm{distribHaarChar}(x)$ of the idele group of $F$, viewed in $\mathbb{R}^{\times}$, assumed to take positive values. Let $\mu,\nu$ be characters of the idele group into $\mathbb{C}^{\times}$ that are continuous, unitary ($|\mu(x)| = |\nu(x)| = 1$) and trivial on the principal ideles. Let $\varphi,\psi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be two families such that, for each $s$, the slice satisfies the induced-section identity $f(bg) = \eta_1(b_{11})\,\eta_2(b_{22})\,f(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero), with $\eta_1 = \mu\,\alpha^{s+1/2}$ and $\eta_2 = \nu\,\alpha^{-(s+1/2)}$; each slice is archimedean $K$-finite (at each infinite place the right translates under the row-isometry subgroup span a finite-dimensional space) and smooth for the finite adelic subgroup (the kernel of the archimedean projection stabilises it openly); the family is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$; at each infinite place all right translations by the row-isometry subgroup of all slices lie in one fixed finite-dimensional space of functions; and the family is flat, $f(s,k) = f(0,k)$ for $k$ in the adelic maximal compact subgroup. Let $O_\varphi, O_\psi \subseteq \mathbb{C}$ be open preconnected sets containing the imaginary axis $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$, and let $E_\varphi,N_\varphi$ (resp. $E_\psi,N_\psi$) be functions of $(s,g)$ analytic in $s$ on the corresponding set for each $g$, jointly continuous there, and agreeing for $\mathrm{Re}\,s > 1/2$ with the partial Eisenstein sum $f(s,g) + \sum_{\xi \in F} f(s, w\,u(\xi)\,g)$ ($w$ the adelic Weyl element, $u(\xi)$ the upper unipotent) and with the Weyl intertwining integral $\int_{\mathbb{A}_F} f(s, w^{-1} u(x) g)\,dx$ for the adelic additive Haar measure, respectively. Put $c = (\mathrm{vol}(\mathrm{adelicBox}))^{-1}$, write $\langle a,b\rangle = \int_{\mathbf{K}} a\,\overline{b}$ for the Haar measure on the adelic maximal compact $\mathbf{K}$, and set $n_\varphi = \|\varphi(0)\|_{L^2(\mathbf{K})}$, $n_\psi = \|\psi(0)\|_{L^2(\mathbf{K})}$, $n_{N\varphi}(t) = \|c\,N_\varphi(it)\|$, $n_{N\psi}(t) = \|c\,N_\psi(it)\|$, $n_{D\varphi}(t) = \|c\,\partial_s N_\varphi|_{s=it}\|$, $n_{D\psi}(t) = \|c\,\partial_s N_\psi|_{s=it}\|$, together with $U(t) = \langle \varphi(it), c\,N_\psi(it)\rangle$, $V(t) = \langle c\,N_\varphi(it), \psi(it)\rangle$, $Q(t) = \langle c\,N_\varphi(it), c\,\partial_s N_\psi|_{s=it}\rangle$, $U'(t) = \langle \varphi(0), c\,i\,\partial_s N_\psi|_{s=it}\rangle$ and $V'(t) = \langle c\,i\,\partial_s N_\varphi|_{s=it}, \psi(0)\rangle$. Then $U, V, Q, U', V'$ are continuous on $\mathbb{R}$; for every $t$ the function $U$ has derivative $U'(t)$ at $t$ and $V$ has derivative $V'(t)$ at $t$; and for every $t$ one has $\|U(t)\| \le n_\varphi\, n_{N\psi}(t)$, $\|V(t)\| \le n_{N\varphi}(t)\, n_\psi$, $\|Q(t)\| \le n_{N\varphi}(t)\, n_{D\psi}(t)$, $\|U'(t)\| \le n_\varphi\, n_{D\psi}(t)$ and $\|V'(t)\| \le n_{D\varphi}(t)\, n_\psi$.
--
--   These are the regularity and size clauses for the Maass–Selberg pairings attached to a flat holomorphic family of $\mathrm{GL}_2$ Eisenstein data restricted to the unitary axis: continuity, differentiation under the integral sign along the axis (flatness removing the $s$-dependence of the sections on the maximal compact subgroup), and Cauchy–Schwarz estimates in $L^2(\mathbf{K})$. They feed the construction of a summable dominant for the continuous-spectrum contribution and the associated bounds on the axis continuation of the truncated inner products.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat.lean

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

theorem AutomorphicForm.continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
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
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
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
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
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
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      ,
    let c : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹
    let nφ : ℝ := Real.sqrt (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nψ : ℝ := Real.sqrt (∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nψ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nDφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let nDψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let U : ℝ → ℂ := fun t =>
      ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let V : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let Q : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let U' : ℝ → ℂ := fun t =>
      ∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
        conj (c * (Complex.I * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let V' : ℝ → ℂ := fun t =>
      ∫ k, c * (Complex.I * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)) *
        conj (ψf 0 (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    Continuous U ∧ Continuous V ∧ Continuous Q ∧ Continuous U' ∧ Continuous V' ∧
    (∀ t : ℝ, HasDerivAt U (U' t) t) ∧ (∀ t : ℝ, HasDerivAt V (V' t) t) ∧
    (∀ t : ℝ, ‖U t‖ ≤ nφ * nNψ t ∧ ‖V t‖ ≤ nNφ t * nψ ∧ ‖Q t‖ ≤ nNφ t * nDψ t ∧
      ‖U' t‖ ≤ nφ * nDψ t ∧ ‖V' t‖ ≤ nDφ t * nψ) := by sorry
