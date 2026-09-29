-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_norm_eulerProduct_of_le_abs_im_of_isInducedSection
-- name    : AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_norm_eulerProduct_of_le_abs_im_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/cc6e0d55-ea8c-515a-bb3d-c907423b8c04
-- title:
--   Growth of the Weyl intertwining operator at large height
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_F$ (assumed pointwise positive, $\alpha(x)>0$). Let $\mu,\nu$ be characters $(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ that are unitary ($\|\chi(x)\|=1$ for all $x$), trivial on the principal ideles $F^\times$, and continuous, and let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: for each $s$, $\varphi_s(bg)=\eta_1(b)\,\eta_2(b)\,\varphi_s(g)$ for $b$ in the adelic Borel, where $\eta_1=\mu\,\alpha^{s+1/2}$ and $\eta_2=\nu\,\alpha^{-(s+1/2)}$ are evaluated at the two diagonal entries of $b$; each $\varphi_s$ is $K_\infty$-finite at every infinite place and a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup under right translation; $\varphi$ is jointly continuous and holomorphic in $s$ for each $g$; and at each infinite place $w$ all the functions $k\mapsto\varphi_s(gk)$ on the row-isometry subgroup at $w$ lie in one finite-dimensional complex subspace, uniformly in $s$ and $g$. Let $Mc:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for each $g$ the function $s\mapsto Mc(s,g)$ is meromorphic in normal form on all of $\mathbb{C}$ and equals the Weyl intertwining integral $\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ (adelic additive Haar measure) for $\operatorname{Re} s>1/2$, and let $\sigma_0>0$. Write $c_v=(\mu\nu^{-1})(\varpi_v)$ at a uniformiser idele when $\mu\nu^{-1}$ is unramified at the finite place $v$ (its local character kills the local units) and $c_v=0$ otherwise, and let $P(w)=\prod_v(1-c_vN(v)^{-w})^{-1}$, the product over all finite places. The conclusion is the conjunction of two assertions. First, if $\mu\nu^{-1}$ is the character $x\mapsto\|x\|^{i\tau}$ of the idele norm for some real $\tau$, then for every entire $Q$ with $Q(w)=(w-(1-i\tau))P(w)$ for $\operatorname{Re} w>1$ there are $T_0\in\mathbb{R}$, $A\ge 0$ and $N\in\mathbb{N}$ such that for all $s$ with $0\le\operatorname{Re} s\le\sigma_0$ and $|\operatorname{Im} s|\ge T_0$, and all $k$ in the adelic maximal compact subgroup (integral finite part, row-isometric archimedean components), $$\|(s-(1/2-i\tau/2))\,Q(2s+1)\,Mc(s,k)\|\le A(1+|\operatorname{Im} s|)^N\|Q(2s)\|\cdot\sup_{k'\in\mathbf{K}}\|\varphi_s(k')\|.$$ Secondly, if $\mu\nu^{-1}$ is not of that form for any real $\tau$, then for every entire $L$ with $L(w)=P(w)$ for $\operatorname{Re} w>1$ there are $T_0$, $A\ge 0$ and $N$ with $\|L(2s+1)Mc(s,k)\|\le A(1+|\operatorname{Im} s|)^N\|L(2s)\|\sup_{k'\in\mathbf{K}}\|\varphi_s(k')\|$ on the same range of $s$ and $k$.
--
--   This is the large-height half of the relative growth bound for the global intertwining operator attached to a principal-series section of $\mathrm{GL}_2$ over a number field: on the part of the strip $0\le\operatorname{Re} s\le\sigma_0$ with $|\operatorname{Im} s|$ beyond a threshold, the continued intertwining operator multiplied by the completed Euler product at $2s+1$ is bounded by a polynomial in $1+|\operatorname{Im} s|$ times the Euler product at $2s$ and the sup-norm of the section on the maximal compact. It is combined with the complementary bound on a bounded height range in [`AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection`](thm.html#AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection), en route to the analytic properties of Eisenstein series used in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_norm_eulerProduct_of_le_abs_im_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
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
    AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_norm_eulerProduct_of_le_abs_im_of_isInducedSection
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
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
      (σ₀ : ℝ) (_hσ₀ : 0 < σ₀),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∀ Q : ℂ → ℂ, Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → T₀ ≤ |s.im| →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Q (2 * s + 1) * Mc s k‖ ≤
              A * (1 + |s.im|) ^ N * ‖Q (2 * s)‖ *
                ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → T₀ ≤ |s.im| →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖L (2 * s + 1) * Mc s k‖ ≤
              A * (1 + |s.im|) ^ N * ‖L (2 * s)‖ *
                ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by sorry
