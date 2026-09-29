-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
-- name    : AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9359434e-b99b-5912-8849-68fac1df5342
-- title:
--   Regularity across Re s=0 of the L-normalised GL(2) intertwining operator
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the real character of the idele group obtained from the module character `distribHaarChar` of the adele ring of $F$, assumed everywhere positive. Let $\mu,\nu$ be characters of the ideles with values in $\mathbb{C}^\times$ which are unitary ($\|\chi(x)\|=1$ for all $x$), trivial on principal ideles, and continuous. Let $\varphi:\mathbb{C}\to GL_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: for each $s$, $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_1)\,\nu\alpha^{-(s+1/2)}(b_2)\,\varphi_s(g)$ for $b$ in the adelic Borel with diagonal entries $b_1,b_2$; each $\varphi_s$ is finite under right translation by the archimedean row-isometry subgroups and a smooth vector for the finite adelic subgroup; $\varphi$ is jointly continuous and differentiable in $s$ for each $g$; and at each infinite place $w$ all functions $k\mapsto\varphi_s(gk)$ on the row-isometry subgroup lie in one finite-dimensional space. Let $Mc$ satisfy, for each $g$, that $s\mapsto Mc\,s\,g$ is meromorphic in normal form on $\mathbb{C}$ and equals the Weyl intertwining integral $\int\varphi_s(w^{-1}u(x)g)\,dx$ for $\mathrm{Re}\,s>1/2$. Write $P(w)$ for the Euler product over all finite places of $(1-c_vN(v)^{-w})^{-1}$, where $c_v=(\mu\nu^{-1})$ of a uniformiser idele at $v$ when $\mu\nu^{-1}$ is unramified at $v$ and $c_v=0$ otherwise. Then: (i) for every real $\tau$ with $\mu\nu^{-1}=\|\cdot\|^{i\tau}$ and every entire $Q$ agreeing with $(w-(1-i\tau))P(w)$ on $\mathrm{Re}\,w>1$, there are an open $U\supseteq\{\mathrm{Re}\,s\ge 0\}$ and $H$ with $H(\cdot,g)$ analytic on a neighbourhood of every point of $U$ for each $g$, $H$ jointly continuous on $U\times GL_2(\mathbb{A}_F)$, and $H(s,g)=(s-(1/2-i\tau/2))\,Q(2s+1)\,Mc\,s\,g$ for $\mathrm{Re}\,s>1/2$; (ii) if $\mu\nu^{-1}$ is no such character, the same conclusion holds for every entire $L$ agreeing with $P$ on $\mathrm{Re}\,w>1$, with $H(s,g)=L(2s+1)\,Mc\,s\,g$ for $\mathrm{Re}\,s>1/2$.
--
--   This is the statement that the intertwining operator on the principal series of $GL(2)$ over the adeles, multiplied by the Hecke $L$-function of $\mu\nu^{-1}$ at $2s+1$ (with the pole factor removed in the case of a norm power), continues holomorphically and jointly continuously across the critical line $\mathrm{Re}\,s=0$. It is used to produce the continued intertwining operator itself and, combined with growth estimates, the polynomial bounds on the regularised operator.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal
open scoped Classical in

theorem
    AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_eulerProduct_mul_intertwining_continuation
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∀ Q : ℂ → ℂ, Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
          ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
            (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
            ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
              H s g = (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * (Q (2 * s + 1) * Mc s g)) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
          ∃ H : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
            (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => H s g) U) ∧
            ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) (U ×ˢ Set.univ) ∧
            ∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
              H s g = L (2 * s + 1) * Mc s g) := by sorry
