-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
-- name    : AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0da68d62-cbd9-5da9-91e7-bffb0aef635a
-- title:
--   L²-continuity of truncated continued Eisenstein families
-- statement:
--   Let $F$ be a number field, and let $0<\alpha<\beta$ be real numbers; let $\Phi F$ be a set of adelic $\mathrm{GL}_2$-points. Write $\alpha m$ for the homomorphism of unit groups $(\mathbb{A}_F)^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring followed by $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha m(x)>0$ for all $x$. Let $\mu,\nu:(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be characters which are unitary ($|\mu(x)|=|\nu(x)|=1$) and idele class characters (trivial on the image of $F^\times$). Let $\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ is an induced section for the characters $\mu\cdot\alpha m^{\,s+1/2}$ and $\nu\cdot\alpha m^{-(s+1/2)}$ of the diagonal entries of the adelic Borel subgroup (lower left entry zero), is archimedean $K$-finite at every infinite place, and is $K_f$-smooth, i.e. its stabiliser in the kernel of $\mathrm{glArch}$ is open; moreover $(s,g)\mapsto\varphi_s(g)$ is jointly continuous, $s\mapsto\varphi_s(g)$ is differentiable for every $g$, and for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing all functions $k\mapsto\varphi_s(gk)$. Let $O\subseteq\mathbb{C}$ be open and preconnected with $\{\operatorname{Re}s>1/2\}\subseteq O$, and let $E_c,N_c:\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be analytic in $s$ on $O$ for each $g$ and jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A}_F)$, with $E_c(s,g)$ equal to the pseudo-Eisenstein sum $\varphi_s(g)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)g)$ and $N_c(s,g)$ equal to the Weyl intertwining integral $\int \varphi_s(w^{-1}n(x)g)\,dx$ against adelic additive Haar measure, whenever $\operatorname{Re}s>1/2$. Assume the rapid-decay hypothesis: for every compact $C\subseteq O$, every compact $\Omega$, every $c'>0$ and every $N\in\mathbb{N}$ there is $M$ such that for $s\in C$, every $b$ in the adelic Borel subgroup with $\alpha m(b_{00})/\alpha m(b_{11})\ge c'$ and every $\omega\in\Omega$, the difference of $E_c(s)$ and its constant term along the unipotents $t\mapsto n(t)$, taken with respect to adelic additive Haar measure conditioned on the adelic box, has norm at most $M\,(\alpha m(b_{00})/\alpha m(b_{11}))^{-N}$ at $b\omega$. Then, for every real $R$, the truncation $\Lambda^{e^R}$ at height $e^R$ for the adelic height, namely $f\mapsto f-\mathbf 1_{\{\mathrm{adelicHeight}>e^R\}}\cdot\mathrm{CT}(f)$ with constant term along $t\mapsto n(t)$ taken against the same conditioned measure, satisfies: (i) $\Lambda^{e^R}E_c(s)$ lies in $L^2$ of the adelic $\mathrm{GL}_2$ Haar measure restricted to the canonical truncation domain for $\alpha,\beta$, for every $s\in O$; and (ii) for every $s_0\in O$, the $L^2$-norm of $\Lambda^{e^R}E_c(s)-\Lambda^{e^R}E_c(s_0)$ on that domain tends to $0$ as $s\to s_0$ within $O$. The data $\Phi F$, the principal level subgroups intersected with the finite-adelic subgroup and the Hecke generators enter only through `productionPinsOf`, of which only the measurable space `nS` on the adeles and the measure `ν`, the conditioned Haar measure on the adelic box, occur.
--
--   This is the square-integrability of truncated Eisenstein series together with continuity of the truncated family in the spectral parameter, in the form needed for the adelic $\mathrm{GL}_2$ spectral theory over a number field. It feeds the Maass–Selberg computations of inner products of truncated Eisenstein series on a determinant slab and the variant of this statement in which the decay hypothesis is replaced by the continuation of the family across the axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family.lean

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

theorem AutomorphicForm.memLp_two_lambdaT_and_tendsto_eLpNorm_lambdaT_sub_restrict_canonicalTruncationDomain_of_rapidlyDecreasing_family
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
      (_hdecay : ∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ O → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ ((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ) →
            ‖Ec s ((b : AdelicGL2 (𝓞 F) F) * ω) -
                AutomorphicForm.constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                  (fun t => AutomorphicForm.unipotentGL2 t) (Ec s) ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤
              M * (((αm (borelDiagFst b) : ℝˣ) : ℝ) / ((αm (borelDiagSnd b) : ℝˣ) : ℝ)) ^ (-(N : ℝ)))
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
