-- Prove2me | Theorems.Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
-- name    : AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/07874a34-8aae-5c55-8110-3bfca686a736
-- title:
--   Meromorphic continuation of the Weyl intertwining integral
-- statement:
--   Let $F$ be a number field with adele ring $\mathbb{A}_F$, and let $\alpha\colon\mathbb{A}_F^{\times}\to\mathbb{R}^{\times}$ be the distributive Haar character of $\mathbb{A}_F$ composed with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and viewed as a homomorphism into units, with $\mathrm{h}\alpha$ the hypothesis that $\alpha(x)>0$ for all $x$. Let $\mu,\nu\colon\mathbb{A}_F^{\times}\to\mathbb{C}^{\times}$ be characters that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all ideles $x$) and trivial on the principal ideles (i.e. $\mu(u)=\nu(u)=1$ for $u\in F^{\times}$ embedded diagonally). Let $\varphi\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, written $\varphi_s$, satisfy: for each $s$, $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (lower-left entry zero), where $\chi_1=\mu\cdot\mathtt{cpowChar}\,\alpha\,(s+\tfrac12)$ and $\chi_2=\nu\cdot\mathtt{cpowChar}\,\alpha\,(-(s+\tfrac12))$; for each $s$ and each infinite place $w$ of $F$, the right translates of $\varphi_s$ under `archRowIsometrySubgroup F w` span a finite-dimensional space; each $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto\varphi_s(g)$ is continuous; and $s\mapsto\varphi_s(g)$ is entire for each $g$. Then for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there is a function $M'\colon\mathbb{C}\to\mathbb{C}$, meromorphic on all of $\mathbb{C}$, with $M'(s)=\int_{\mathbb{A}_F}\varphi_s\bigl(w^{-1}n(x)g\bigr)\,dx$ whenever $\operatorname{Re}s>\tfrac12$, the integral being taken against the additive Haar measure of $\mathbb{A}_F$ for its Borel $\sigma$-algebra, with $w$ the adelic Weyl element and $n(x)$ the upper unipotent matrix.
--
--   This is the meromorphic continuation in $s$ of the intertwining operator attached to the Weyl element acting on the principal-series sections $\varphi_s$ induced from the Borel subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$; only agreement with the convergent integral on the half-plane $\operatorname{Re}s>1/2$ is asserted, not a functional equation or an explicit formula. It supplies the intertwining term in the continuation of the adelic Eisenstein series and is used by the statements about the convolution operator acting on the continued intertwining integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.weylIntertwiningIntegral_meromorphicOn_of_isInducedSection_family
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
      (g : AdelicGL2 (𝓞 F) F),
    letI := adeleBorel (𝓞 F) F
    ∃ M' : ℂ → ℂ, MeromorphicOn M' Set.univ
      ∧ ∀ s : ℂ, 1 / 2 < s.re → M' s
        = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g := by sorry
