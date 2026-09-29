-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
-- name    : AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/55ab219c-ee66-5f2f-82d2-5870fc8ed31d
-- title:
--   L² continuity in s of truncated Eisenstein families
-- statement:
--   Let $F$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi F$ be a subset of $\mathrm{GL}_2$ of the adeles of $F$. Write $\alpha m$ for the idelic modulus, the character of the idele group obtained from the distributive Haar character of the adele ring by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume it takes positive values. Let $\mu,\nu$ be characters of the idele group with values in $\mathbb{C}^\times$ that are unitary ($|\chi(x)|=1$ for all $x$), trivial on the principal ideles $F^\times$, and continuous. Let $\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ satisfies $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup, with $\chi_1=\mu\cdot\alpha m^{s+1/2}$ and $\chi_2=\nu\cdot\alpha m^{-(s+1/2)}$; such that at each infinite place the right translates of $\varphi_s$ under the row-isometry subgroup span a finite-dimensional space; such that the stabiliser of $\varphi_s$ in the kernel of the archimedean projection is open; jointly continuous in $(s,g)$, entire in $s$, and with all the functions $k\mapsto\varphi_s(gk)$ on the row-isometry subgroup at a fixed infinite place lying in one finite-dimensional subspace independent of $s$ and $g$. Let $O\subseteq\mathbb{C}$ be open and preconnected with $\{\operatorname{Re}s>1/2\}\subseteq O$, and let $Ec,Nc$ be functions of $(s,g)$ that are analytic on a neighbourhood of each point of $O$ in $s$ for each fixed $g$, jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A}_F)$, and for $\operatorname{Re}s>1/2$ equal respectively to the pseudo-Eisenstein sum $\varphi_s(g)+\sum_{b\in F}\varphi_s(w\,n(b)g)$ and to the Weyl intertwining integral $\int \varphi_s(w^{-1}n(x)g)\,dx$ against the additive adelic Haar measure. Let $R$ be real, and let $\Lambda$ denote the truncation $\Lambda f(g)=f(g)-\mathbf{1}_{\{\text{adelic height}>e^R\}}(g)\cdot\int f(n(t)g)\,d\nu_0(t)$, with $\nu_0$ the additive adelic Haar measure conditioned on the adelic box and $n(t)$ the upper unipotent. Then: for every $s\in O$ the function $\Lambda(Ec\,s)$ lies in $L^2$ of the Haar measure of $\mathrm{GL}_2(\mathbb{A}_F)$ restricted to the canonical truncation domain attached to $(\alpha,\beta)$; and for every $s_0\in O$ the $L^2$ norm of $\Lambda(Ec\,s)-\Lambda(Ec\,s_0)$ on that domain tends to $0$ as $s\to s_0$ within $O$.
--
--   This is the statement that truncated Eisenstein series, given analytically continued data on a region $O$ containing the half-plane $\operatorname{Re}s>1/2$, are square-integrable on the canonical truncation domain of the determinant slab $\alpha<\cdot<\beta$ and depend continuously on the spectral parameter in that $L^2$ norm. It is used by the Maass–Selberg computations on the slab, which transport by continuity an identity first proved for parameters with distinct real parts to the remaining parameters, and by the spectral-side statements on the unitary axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family.lean

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

theorem AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_axis_continuation_family
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hO : IsOpen O) (_hOc : IsPreconnected O) (_hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O)
      (_hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
      (_hNa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) O)
      (_hEjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ))
      (_hNjc : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (O ×ˢ Set.univ))
      (_hE : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = AutomorphicForm.pseudoEisenstein F (φ s) g)
      (_hN : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
      (R : ℝ),
    (∀ s ∈ O, MemLp (fun x : AdelicGL2 (𝓞 F) F => (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s)) x) 2
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F α β))) ∧
    ∀ s₀ ∈ O, Filter.Tendsto
        (fun s : ℂ => eLpNorm (fun x : AdelicGL2 (𝓞 F) F => (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s)) x - (@AutomorphicForm.lambdaT _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
          (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
            (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
          (Ec s₀)) x) 2
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (AutomorphicForm.canonicalTruncationDomain F α β)))
        (nhdsWithin s₀ O) (nhds 0) := by sorry
