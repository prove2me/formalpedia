-- Prove2me | Theorems.Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
-- name    : AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/4fbeb7ea-4a69-550e-8c86-4a030aca292f
-- title:
--   Euler factors normalising the Weyl intertwining integral
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the module `distribHaarChar` of the adele ring by viewing its values in $\mathbb{R}_{\ge 0}$ as real units, assumed to take strictly positive values ($h\alpha$). Let $\mu,\nu\colon (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be characters that are unitary in the sense that $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$, and let $\varphi\colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for every $s$, $\varphi_s(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero), where $\chi_1 = \mu\cdot\alpha^{s+1/2}$ and $\chi_2 = \nu\cdot\alpha^{-(s+1/2)}$ via `cpowChar`; for every $s$ and every infinite place $w$, the right translates of $\varphi_s$ under `archRowIsometrySubgroup F w` span a finite-dimensional space, and $\varphi_s$ is a smooth vector for the finite-adelic subgroup `finiteAdelicGL2Subgroup F`; $(s,g)\mapsto \varphi_s(g)$ is continuous; and $s \mapsto \varphi_s(g)$ is differentiable on all of $\mathbb{C}$ for each $g$. Fix $g \in \mathrm{GL}_2(\mathbb{A}_F)$. Then, with the adeles carrying their Borel $\sigma$-algebra, there are a finite set $S$ of finite places of $F$, units $\varpi_v$ of each completion $F_v$ with $v(\varpi_v)$ equal to $\mathrm{ofAdd}(-1)$, and a function $R\colon\mathbb{C}\to\mathbb{C}$ meromorphic on $\mathbb{C}$ and differentiable on $\{\operatorname{Re} s > 0\}$, such that for every $s$ with $\operatorname{Re} s > 1/2$, writing $\chi_v$ for the local component at $v$ of $\chi = \mu\nu^{-1}$ and $Nv = |\mathcal{O}_F/v|$, $$\prod_{v \notin S}\bigl(1 - \chi_v(\varpi_v)\,Nv^{-2s}\bigr)\cdot \int_{\mathbb{A}_F} \varphi_s\bigl(w^{-1}\,n(x)\,g\bigr)\,dx = \prod_{v \notin S}\bigl(1 - \chi_v(\varpi_v)\,Nv^{-(2s+1)}\bigr)\cdot R(s),$$ the products being unconditional infinite products over the places outside $S$, $w$ the adelic Weyl element, $n(x)$ the unipotent matrix with upper-right entry $x$, and the integral a Bochner integral against the additive Haar measure of $\mathbb{A}_F$.
--
--   This is the analytic continuation of the $\mathrm{GL}_2$ Weyl intertwining (constant-term) integral in the form needed for Eisenstein series: after multiplication by a partial Euler product of the ratio character $\mu\nu^{-1}$, the integral agrees on $\operatorname{Re} s > 1/2$ with a ratio whose remaining factor is meromorphic on the plane and holomorphic on $\operatorname{Re} s > 0$, reflecting the Gindikin–Karpelevich factorisation $\Lambda(2s)/\Lambda(2s+1)$. It is used by the statements continuing the Bruhat–Eisenstein series and its constant term, and the estimates on their difference, for archimedean-$K$-finite holomorphic families of induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal
set_option autoImplicit false

theorem AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∃ R : ℂ → ℂ, MeromorphicOn R Set.univ ∧ DifferentiableOn ℂ R {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 / 2 < s.re →
          (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s))))
            * weylIntertwiningIntegral (𝓞 F) F
                (NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F) (φ s) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
            * R s := by sorry
