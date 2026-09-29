-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ff57c6f1-2345-56b9-8d70-9ec9101bac71
-- title:
--   Analytic continuation and rapid decay of the non-constant part of Eₛ
-- statement:
--   Let $F$ be a number field and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the distributive Haar character `distribHaarChar` of the adele ring $\mathbb{A}_F$ of $F$ composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed everywhere positive (hypothesis $h\alpha$). Let $\varphi : \mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that: for every $s$, $\varphi_s$ is an induced section for the pair of characters $\mathrm{cpowChar}(\alpha)^{s+1/2}$ and $\mathrm{cpowChar}(\alpha)^{-(s+1/2)}$, i.e. $\varphi_s(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi_s(g)$ for every $b$ in the adelic Borel subgroup (the matrices with $b_{10}=0$) and every $g$, where $b_{00},b_{11}$ are the diagonal entries viewed as ideles; for every $s$, $\varphi_s$ is `IsArchKFinite` (archimedean $K$-finite at each infinite place of $F$) and `IsKfSmooth` (a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup); $(s,g)\mapsto\varphi_s(g)$ is continuous; and $s\mapsto\varphi_s(g)$ is entire for each $g$. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}^{\prime}\varphi_s\bigl(w\, n(\xi)\, h\bigr)$, the sum being the unconditional sum over $\xi\in F$, with $w$ the image of the Weyl element under $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and set $\mathrm{hgt}(b)=\alpha(b_{00})/\alpha(b_{11})\in\mathbb{R}$ for $b$ in the adelic Borel subgroup. Then there exists $W_{\mathrm{nc}} : \mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that: (i) for each $h$, $s\mapsto W_{\mathrm{nc}}(s,h)$ is analytic on a neighbourhood of each point of $\{\operatorname{Re} s>0\}$; (ii) for $\operatorname{Re} s>1/2$ and all $h$, $W_{\mathrm{nc}}(s,h)=E_s(h)-\mathrm{constantTerm}(\mu,\,n,\,E_s)(h)$, where $\mu$ is the additive Haar measure of $\mathbb{A}_F$ conditioned on the adelic box (infinite box times integral finite adeles) and the constant term is the corresponding integral of `constantTermIntegrand` for the unipotent family $n$; (iii) $(s,h)\mapsto W_{\mathrm{nc}}(s,h)$ is continuous on $\{\operatorname{Re} s>0\}\times\mathrm{GL}_2(\mathbb{A}_F)$; and (iv) for every compact $C\subseteq\{\operatorname{Re} s>0\}$, every compact $\Omega\subseteq\mathrm{GL}_2(\mathbb{A}_F)$, every $c'>0$ and every $N\in\mathbb{N}$ there is $M\in\mathbb{R}$ with $\|W_{\mathrm{nc}}(s,b\omega)\|\le M\,\mathrm{hgt}(b)^{-N}$ for all $s\in C$, all $\omega\in\Omega$ and all $b$ in the adelic Borel subgroup with $\mathrm{hgt}(b)\ge c'$.
--
--   This is the non-constant-term half of the uniform moderate growth statement for the spherical Eisenstein family built from Bruhat-cell sections: the difference between $E_s$ and its constant term along the unipotent radical continues analytically to $\operatorname{Re} s>0$ and decays faster than any power of the height in Siegel sets, locally uniformly in $s$. It is combined with the corresponding analysis of the intertwining integral in [`AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_analyticOnNhd_sub_one_half_mul_bruhatEisenstein_norm_le_archHeight_pow_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ Wnc : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Wnc s h) {s : ℂ | 0 < s.re}) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        Wnc s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            unipotentGL2 (E s) h) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Wnc p.1 p.2)
        ({s : ℂ | 0 < s.re} ×ˢ Set.univ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ {s : ℂ | 0 < s.re} → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            ‖Wnc s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by sorry
