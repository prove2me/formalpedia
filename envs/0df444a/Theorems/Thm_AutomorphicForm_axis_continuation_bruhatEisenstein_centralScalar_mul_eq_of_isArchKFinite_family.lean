-- Prove2me | Theorems.Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
-- name    : AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/a4802d6f-ec57-549e-b81d-c9e178c9f6ec
-- title:
--   Central character μν of the continued Eisenstein series
-- statement:
--   Let $F$ be a number field, and let $\alpha_m$ denote the monoid homomorphism from the ideles $(\mathbb{A}_F)^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_F$ pushed into $\mathbb{R}$ and restricted to units, assumed pointwise positive. Let $\mu,\nu:(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be monoid homomorphisms that are unitary ($|\chi(x)|=1$ for all $x$), trivial on the principal ideles coming from $F^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\varphi:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ is an induced section for the pair $(\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)})$, i.e. $\varphi_s(bg)$ equals the product of the two characters evaluated at the two diagonal entries of $b$ times $\varphi_s(g)$ for $b$ in the adelic Borel subgroup; each $\varphi_s$ is archimedean $K$-finite at every infinite place and a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup under right translation; $\varphi$ is jointly continuous; $s\mapsto\varphi_s(g)$ is entire; and for each infinite place $w$ there is a finite-dimensional subspace of functions on `archRowIsometrySubgroup F w` containing all right translates $k\mapsto\varphi_s(gk)$. Let $O_\varphi\subseteq\mathbb{C}$ and $E_\varphi,N_\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: $O_\varphi$ is open and preconnected and contains both the axis $\mathrm{Re}\,s=0$ and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ both $s\mapsto E_\varphi(s,g)$ and $s\mapsto N_\varphi(s,g)$ are analytic on a neighbourhood of each point of $O_\varphi$; both are jointly continuous on $O_\varphi\times\mathrm{GL}_2(\mathbb{A}_F)$; for $\mathrm{Re}\,s>1/2$, $E_\varphi(s,g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)\,g)$ with $w$ the adelic Weyl element and $n(\xi)$ the upper unipotent matrix; and for $\mathrm{Re}\,s>1/2$, $N_\varphi(s,g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ against adelic additive Haar measure. Then for every $s\in O_\varphi$, every idele $z$ and every $g\in\mathrm{GL}_2(\mathbb{A}_F)$, $E_\varphi(s,\ \mathrm{diag}(z,z)\,g)=\mu(z)\nu(z)\,E_\varphi(s,g)$.
--
--   This records that the analytically continued Eisenstein family attached to a pair of Hecke characters has central character $\mu\nu$, the central-scalar counterpart of its left invariance under global points. It is used downstream in the analytic study of this family — in the $L$-function and Paley–Wiener statements, and in growth estimates for the continued series on Siegel sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.axis_continuation_bruhatEisenstein_centralScalar_mul_eq_of_isArchKFinite_family
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
      (s : ℂ) (_hs : s ∈ Oφ) (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
    Eφ s (AutomorphicForm.centralScalar (𝓞 F) F z * g) = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * Eφ s g := by sorry
