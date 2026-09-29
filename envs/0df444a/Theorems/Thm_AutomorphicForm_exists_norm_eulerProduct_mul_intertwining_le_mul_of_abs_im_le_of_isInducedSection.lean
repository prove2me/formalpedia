-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
-- name    : AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c9203eff-1b91-5efa-8fa9-a9654602b947
-- title:
--   Bounded strips: relative bound for the continued intertwining operator
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the distributive Haar character of the adele ring, viewed in $\mathbb{R}^\times$, assumed pointwise positive. Let $\mu,\nu$ be characters of $(\mathbb{A}_F)^\times$ in $\mathbb{C}^\times$ that are unitary ($\|\chi(x)\|=1$ for all ideles), trivial on the principal ideles $F^\times$, and continuous. Let $\varphi:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that each $\varphi_s$ satisfies $\varphi_s(bg)=\chi_1(b_1)\chi_2(b_2)\varphi_s(g)$ for $b$ in the adelic Borel subgroup with diagonal entries $b_1,b_2$, where $\chi_1=\mu\,\alpha^{s+1/2}$ and $\chi_2=\nu\,\alpha^{-(s+1/2)}$; each $\varphi_s$ is archimedean $K$-finite and smooth for right translation by the finite adelic subgroup; $\varphi$ is jointly continuous and holomorphic in $s$ for each $g$; and at each infinite place $w$ all right translates $k\mapsto\varphi_s(gk)$ by the row-isometry subgroup at $w$ lie in one finite-dimensional space of functions. Let $Mc$ be such that for each $g$ the function $s\mapsto Mc\,s\,g$ is meromorphic in normal form on all of $\mathbb{C}$ and equals the Weyl intertwining integral $\int \varphi_s(w^{-1}u(x)g)\,dx$ against adelic additive Haar measure for $\operatorname{Re} s>1/2$; let $\sigma_0>0$. Write $c_v=(\mu\nu^{-1})(\text{uniformiser idele at }v)$ when $\mu\nu^{-1}$ is unramified at $v$, i.e. its local character is trivial on the units of the local integers, and $c_v=0$ otherwise, and let the Euler product be $\prod_v(1-c_v N(v)^{-w})^{-1}$ over all finite places of $F$ (the subtype complementary to the empty finite set). The conclusion is a conjunction of two implications. First, if $\mu\nu^{-1}$ equals the character $x\mapsto |x|^{i\tau}$ for a real $\tau$, then for every entire $Q$ with $Q(w)=(w-(1-i\tau))\prod_v(1-c_vN(v)^{-w})^{-1}$ for $\operatorname{Re} w>1$ and every real $T_0$ there is $A\ge 0$ with $\|(s-(1/2-i\tau/2))\,Q(2s+1)\,Mc\,s\,k\|\le A\sup_{k'}\|\varphi_s(k')\|$ for all $s$ with $0\le\operatorname{Re} s\le\sigma_0$, $|\operatorname{Im} s|\le T_0$ and all $k$ in the adelic maximal compact subgroup (finite part integral, archimedean components row isometries), the supremum being over that subgroup. Second, if $\mu\nu^{-1}$ is not of the form $|\cdot|^{i\tau}$ for any real $\tau$, then for every entire $L$ agreeing with the Euler product for $\operatorname{Re} w>1$ and every real $T_0$ there is $A\ge0$ with $\|L(2s+1)\,Mc\,s\,k\|\le A\sup_{k'}\|\varphi_s(k')\|$ on the same region and for the same $k$.
--
--   This is the bounded-height half of a relative growth estimate for the meromorphically continued Weyl intertwining operator on the principal series of $\mathrm{GL}_2$ over a number field: on the part of the strip $0\le\operatorname{Re} s\le\sigma_0$ with $|\operatorname{Im} s|\le T_0$, the operator multiplied by the relevant completed Euler factor at $2s+1$ (with the pole factor removed in the degenerate case $\mu\nu^{-1}=|\cdot|^{i\tau}$) is dominated by the sup-norm of the section over the maximal compact subgroup. It feeds the full estimate [`AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection`](thm.html#AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection), where the dependence on $|\operatorname{Im} s|$ is made explicit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection.lean

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
    AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_of_abs_im_le_of_isInducedSection
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
        ∀ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → |s.im| ≤ T₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Q (2 * s + 1) * Mc s k‖ ≤
              A * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∀ T₀ : ℝ, ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ → |s.im| ≤ T₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖L (2 * s + 1) * Mc s k‖ ≤
              A * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by sorry
