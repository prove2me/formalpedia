-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
-- name    : AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/f2f34def-d7df-515a-88f4-4bb419f1f458
-- title:
--   Admissibility of the continued Weyl intertwining integral on the axis
-- statement:
--   Let $F$ be a number field, write $\mathbb{A}$ for its adele ring, and let $\alpha:\mathbb{A}^\times\to\mathbb{R}^\times$ be the module character obtained from `distribHaarChar` of $\mathbb{A}$ via $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed everywhere positive; the adele ring carries its Borel structure and $\mathrm{GL}_2(\mathbb{A})$ the Borel structure used for the group. Let $\mu,\nu:\mathbb{A}^\times\to\mathbb{C}^\times$ satisfy $|\mu(x)|=|\nu(x)|=1$ for all $x$, be trivial on the image of $F^\times$, and be continuous; let $N$ be an ideal of $\mathcal{O}_F$. Let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$, written $\varphi_s$, satisfy: each $\varphi_s$ is an induced section for the pair $(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$, i.e. $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_{00})\,\nu\alpha^{-(s+1/2)}(b_{11})\,\varphi_s(g)$ for every $b$ with $b_{10}=0$; each $\varphi_s$ has finite-dimensional span of right translates under the row-isometry subgroup at each infinite place; each $\varphi_s$ has open stabiliser under right translation by the kernel of the archimedean projection of $\mathrm{GL}_2(\mathbb{A})$; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire; for each infinite place $w$ there is one finite-dimensional space $W$ of functions on `archRowIsometrySubgroup F w` containing $k\mapsto\varphi_s(gk)$ for all $s,g$; and $\varphi_s(gu)=\varphi_s(g)$ for $u$ in `principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`. Let $O\subseteq\mathbb{C}$ and $E,\mathcal{N}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ be continuation data: $O$ is open, preconnected, contains $\{\operatorname{Re}s=0\}$ and $\{\operatorname{Re}s>1/2\}$; $s\mapsto E_s(g)$ and $s\mapsto\mathcal{N}_s(g)$ are analytic on a neighbourhood of each point of $O$; both are jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A})$; and for $\operatorname{Re}s>1/2$ one has $E_s(g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)\,g)$ and $\mathcal{N}_s(g)=\int_{\mathbb{A}}\varphi_s(w^{-1}u(x)g)\,dx$ against `adelicAddHaar`, where $w$ is the adelic Weyl element and $u(x)$ the upper unipotent. Then for every $t\in\mathbb{R}$, setting $M_t(g)=\operatorname{vol}(\mathrm{adelicBox})^{-1}\mathcal{N}_{it}(g)$: $M_t$ is an induced section for $(\nu\alpha^{-it+1/2},\mu\alpha^{it-1/2})$, namely the pair $(\mathrm{etaFst}\ \nu\ (-it),\mathrm{etaSnd}\ \mu\ (-it))$; $M_t$ is continuous; $\mathcal{N}_{it}(gu)=\mathcal{N}_{it}(g)$ for all $g$ and all $u$ in `principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F`; and for each infinite place $w$ there is a finite-dimensional space $W$ of functions on `archRowIsometrySubgroup F w` with $k\mapsto M_t(gk)$ in $W$ for every $g$.
--
--   This is the statement that the analytic continuation of the Weyl intertwining operator to the unitary axis $s=it$ carries an admissible family of induced sections to an admissible section of the swapped induced representation: the induction identity, continuity, right invariance under the principal level at $N$ and uniform $K_\infty$-finiteness all survive the continuation. It feeds the axis pairings and inner-product identities for the Eisenstein series attached to $(\mu,\nu)$, where the normalised constant term $\operatorname{vol}^{-1}\mathcal{N}_{it}$ must itself be treated as an automorphic section of the same level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel.lean

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
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
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
      (N : Ideal (𝓞 F))
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
      (t : ℝ),
    IsInducedSection (𝓞 F) F (etaFst ν αm hαm (-((t : ℂ) * Complex.I))) (etaSnd μ αm hαm (-((t : ℂ) * Complex.I)))
        (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) ∧
    Continuous (fun g => ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) g) ∧
    (∀ (g : AdelicGL2 (𝓞 F) F), ∀ u ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
        Nφ ((t : ℂ) * Complex.I) (g * u) = Nφ ((t : ℂ) * Complex.I) g) ∧
    (∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) =>
            ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ * Nφ ((t : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) := by sorry
