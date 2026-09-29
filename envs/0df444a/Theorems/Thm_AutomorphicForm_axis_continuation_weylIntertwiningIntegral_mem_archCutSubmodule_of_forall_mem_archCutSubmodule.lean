-- Prove2me | Theorems.Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
-- name    : AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d4fe794e-d51d-5a05-a08a-63e127ed8dee
-- title:
--   Continued Weyl intertwining integral preserves archimedean types
-- statement:
--   Let $F$ be a number field, and let `tysF` be an archimedean type family: for each infinite place $w$ a natural number together with that many finite-dimensional representations of the determinant-one row-isometry group of the completion $F_w$. Write $\alpha$ for the monoid homomorphism $\mathbb{A}_F^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters with $|\mu(x)|=|\nu(x)|=1$ for all $x$, trivial on the image of $F^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\varphi:\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C})$ satisfy: for each $s$, $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_{11})\,\nu\alpha^{-(s+1/2)}(b_{22})\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup; for each $s$ and each infinite place $w$ the right translates of $\varphi_s$ under the archimedean row-isometry subgroup at $w$ span a finite-dimensional space, and the stabiliser of $\varphi_s$ in the kernel of the archimedean projection is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is differentiable; at each $w$ one fixed finite-dimensional space $W$ contains all the right $K_w$-translate functions $k\mapsto\varphi_s(gk)$, for all $s$ and $g$; and $\varphi_s$ lies in `archCutSubmodule F tysF`, the intersection over infinite places $w$ of the sum of the isotypic submodules attached to the listed representations at $w$. Let $O\subseteq\mathbb{C}$ be open and preconnected, containing the imaginary axis and the half-plane $\operatorname{Re} s>1/2$, and let $E_s,N_s$ be functions on $\mathrm{GL}_2(\mathbb{A}_F)$ that are analytic on a neighbourhood of each point of $O$ in $s$ for each fixed $g$, jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A}_F)$, and that for $\operatorname{Re} s>1/2$ are given by $E_s(g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w_0 n(\xi)g)$ and by $N_s(g)=\int_{\mathbb{A}_F}\varphi_s(w_0^{-1}n(x)g)\,dx$ against additive Haar measure, $w_0$ the adelic Weyl element and $n(x)$ the upper unipotent matrix. Then for every real $t$ the function $N_{it}$ lies in `archCutSubmodule F tysF`.
--
--   This is the statement that the Weyl (Gindikin–Karpelevich) intertwining operator preserves archimedean $K$-types, and that this persists to the analytic continuation of the operator onto the unitary axis. It is used in the spectral analysis of the pseudo-Eisenstein and residual parts of the $\mathrm{GL}_2$ cuspidal decomposition, where the continued intertwining image must stay inside the fixed finite collection of archimedean types.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule.lean

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
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
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

open AutomorphicForm

theorem AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (tysF : ArchTypeFamily F) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
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
      (_hφfty : ∀ s : ℂ, φf s ∈ archCutSubmodule F tysF)
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
    Nφ ((t : ℂ) * Complex.I) ∈ archCutSubmodule F tysF := by sorry
