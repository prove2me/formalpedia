-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
-- name    : AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/f26c9aca-b444-55b2-b7a1-e2d209ad221c
-- title:
--   Regularity of the continued intertwining operator on Re s≥ 0
-- statement:
--   Let $F$ be a number field and let $\alpha\colon(\mathbb{A}_F)^\times\to\mathbb{R}^\times$ be the unit-valued character obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` of the adele ring by passing from $\mathbb{R}_{\ge 0}$ to $\mathbb{R}$, assumed throughout to take positive values ($h\alpha$). Let $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be characters that are unitary ($\lVert\chi(x)\rVert=1$ for all $x$), trivial on the principal ideles $F^\times$, and continuous. Let $\varphi\colon\mathbb{C}\to GL_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for each $s$ the function $\varphi_s$ is an induced section for the pair $(\mu\cdot\mathtt{cpowChar}\,\alpha\,h\alpha\,(s+\tfrac12),\ \nu\cdot\mathtt{cpowChar}\,\alpha\,h\alpha\,(-(s+\tfrac12)))$, i.e. $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup; each $\varphi_s$ satisfies `IsArchKFinite` (at every infinite place $w$ its right translates under `archRowIsometrySubgroup F w`, the image of the row isometry subgroup of $GL_2(F_w)$, satisfy `RightTranslatesSpanFinite`) and `IsKfSmooth` (it is a smooth vector for right translation by `finiteAdelicGL2Subgroup F`); $(s,g)\mapsto\varphi_s(g)$ is jointly continuous and $s\mapsto\varphi_s(g)$ is entire for each $g$; and a uniform archimedean type hypothesis holds: for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup F w` containing $k\mapsto\varphi_s(gk)$ for all $s$ and $g$. Let $Mc\colon\mathbb{C}\to GL_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for every $g$ the function $s\mapsto Mc(s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$ and equals the Weyl intertwining integral $\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$, taken with respect to the adelic additive Haar measure, whenever $\tfrac12<\operatorname{Re}s$. The conclusion is a conjunction of two implications. First, for every real $\tau$ with $\mu\nu^{-1}=$ [`NumberField.TateGlobal.normPowChar F τ`](def/NumberField_NormPowChar.html#L22) (the character $x\mapsto\lVert x\rVert^{i\tau}$ built from the idele norm), there exist an open $U\subseteq\mathbb{C}$ containing $\{\operatorname{Re}s\ge 0\}$ and a function $Mreg$ on $\mathbb{C}\times GL_2(\mathbb{A}_F)$ such that $s\mapsto Mreg(s)(g)$ is analytic on a neighbourhood of $U$ for every $g$, $(s,g)\mapsto Mreg(s)(g)$ is continuous on $U\times GL_2(\mathbb{A}_F)$, and $Mreg(s)(g)=(s-(\tfrac12-\tfrac{\tau}{2}i))\,Mc(s)(g)$ for all $g$ and all $s\in U$ with $s\neq\tfrac12-\tfrac{\tau}{2}i$. Second, if $\mu\nu^{-1}$ is not `normPowChar F τ` for any real $\tau$, there is an open $U\supseteq\{\operatorname{Re}s\ge 0\}$ on which $s\mapsto Mc(s)(g)$ is analytic for every $g$ and $(s,g)\mapsto Mc(s)(g)$ is continuous on $U\times GL_2(\mathbb{A}_F)$.
--
--   This is the regularity statement for the analytically continued Weyl intertwining (constant-term) operator attached to a holomorphic family of Borel-induced sections on $GL_2(\mathbb{A}_F)$: on an open neighbourhood of the closed half-plane $\operatorname{Re}s\ge 0$ its only possible singularity is a simple pole at $s=\tfrac12-i\tau/2$, occurring only when $\mu\nu^{-1}$ is the idele-norm character of exponent $i\tau$. It is obtained from the corresponding statement for the Euler-product normalisation together with the Hecke $L$-function input of global Tate theory, and it feeds the computation of inner products of pseudo-Eisenstein series in [`AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab`](thm.html#AutomorphicForm.setIntegral_pseudoEisenstein_mul_conj_eq_inner_residualProj_add_sum_integral_axis_pairing_slab).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_isOpen_analyticOnNhd_continuousOn_intertwining_continuation_of_isInducedSection
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
      ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
        ∃ Mreg : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
          (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => Mreg s g) U) ∧
          ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mreg p.1 p.2) (U ×ˢ Set.univ) ∧
          ∀ s ∈ U, s ≠ ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I) →
            ∀ g : AdelicGL2 (𝓞 F) F, Mreg s g = (s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Mc s g) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
        (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s : ℂ => Mc s g) U) ∧
        ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Mc p.1 p.2) (U ×ˢ Set.univ)) := by sorry
