-- Prove2me | Theorems.Thm_AutomorphicForm_limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp
-- name    : AutomorphicForm.limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6f3aaa45-9046-5c54-9dff-fced29a3c0fb
-- title:
--   Axis limit of the convolved intertwining datum
-- statement:
--   Let $K$ be a number field, write $\mathbb{A}=\mathbb{A}_K$ for its adele ring with its Borel $\sigma$-algebra, and let $\alpha_m\colon\mathbb{A}^\times\to\mathbb{R}^\times$ be the character obtained from the distributive Haar character of $\mathbb{A}$ through $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed pointwise positive. Let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ satisfy $\|\mu(x)\|=\|\nu(x)\|=1$ for all $x$. Let $\psi_f\colon\mathbb{C}\to GL_2(\mathbb{A})\to\mathbb{C}$ be jointly continuous in $(s,g)$ and such that each $\psi_f(s)$ transforms under the adelic Borel subgroup by $\psi_f(s)(bg)=\eta_1(b_{11})\eta_2(b_{22})\psi_f(s)(g)$, with $\eta_1=\mu\cdot\alpha_m^{s+1/2}$, $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$. Let $O_\psi\subseteq\mathbb{C}$ be open and preconnected, containing $\{\operatorname{Re}s=0\}$ and $\{\operatorname{Re}s>1/2\}$, and let $E_\psi,N_\psi$ be functions of $(s,g)$ which are analytic in $s$ on a neighbourhood of each point of $O_\psi$ for fixed $g$, jointly continuous on $O_\psi\times GL_2(\mathbb{A})$, and which for $\operatorname{Re}s>1/2$ agree respectively with $\psi_f(s)(g)+\sum'_{\xi\in K}\psi_f(s)(w\,u(\xi)g)$ ($w$ the global Weyl element, $u(\xi)$ upper unipotent) and with $\int\psi_f(s)(w^{-1}u(x)g)\,dx$ against adelic additive Haar measure. Let $f$ be continuous with compact support on $GL_2(\mathbb{A})$ and let $M'_c$ be such that $s\mapsto M'_c(s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$ for every $g$ and equals the Weyl intertwining integral of the right convolution $\mathrm{convOp}\,K\,f\,(\psi_f(s))$ for $\operatorname{Re}s>1/2$. Then for every $t\in\mathbb{R}$ and every $g\in GL_2(\mathbb{A})$, the limit of $s\mapsto M'_c(s)(g)$ along the punctured neighbourhood filter of $-it$ equals $(\mathrm{convOp}\,K\,f\,(N_\psi(-it)))(g)$.
--
--   This identifies the meromorphic continuation of the intertwining integral of the convolved family $s\mapsto R(f)\psi_s$ on the unitary axis with $R(f)$ applied to the continued intertwining datum $N_\psi$ of the original family, the shape in which the datum enters the spectral decomposition of pseudo-Eisenstein series. It is used in the computation of the inner product of a pseudo-Eisenstein series with a convolved one, via an identity principle from the half-plane $\operatorname{Re}s>1/2$ together with the commutation of right convolution and the Weyl intertwining integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp.lean

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

theorem AutomorphicForm.limUnder_nhdsNE_eq_convOp_axis_continuation_weylIntertwiningIntegral_of_meromorphicNFOn_of_eq_weylIntertwiningIntegral_convOp
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
      (Mc' : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hMc' : ∀ g : AdelicGL2 (𝓞 K) K, MeromorphicNFOn (fun s : ℂ => Mc' s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
          Mc' s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (convOp K f (ψf s)) g),
    ∀ (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
      Filter.limUnder (nhdsWithin (-((t : ℂ) * Complex.I)) {-((t : ℂ) * Complex.I)}ᶜ) (fun s : ℂ => Mc' s g) =
        convOp K f (Nψ (-((t : ℂ) * Complex.I))) g := by sorry
