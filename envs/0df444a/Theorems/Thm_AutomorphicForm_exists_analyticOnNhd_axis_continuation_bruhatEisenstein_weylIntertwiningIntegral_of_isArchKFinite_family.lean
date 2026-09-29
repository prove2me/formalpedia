-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4543adb3-9ea7-56d5-9ffc-c16deb44d5d0
-- title:
--   Analytic continuation of the Eisenstein and intertwining families
-- statement:
--   Let $F$ be a number field and let $\alpha \colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the module character of the ideles, obtained from `distribHaarChar` of the adele ring composed with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passed to units; $h\alpha$ asserts $\alpha(x) > 0$ for all $x$. Let $\mu, \nu \colon \mathbb{A}_F^\times \to \mathbb{C}^\times$ be homomorphisms that are unitary ($|\mu(x)| = |\nu(x)| = 1$ for all ideles $x$), trivial on the principal ideles $F^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\varphi \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for every $s$, $\varphi_s$ transforms under the adelic Borel subgroup by the pair of characters $\mathrm{etaFst}(\mu,\alpha,s) = \mu\,\alpha^{s+1/2}$ and $\mathrm{etaSnd}(\nu,\alpha,s) = \nu\,\alpha^{-(s+1/2)}$ applied to the two diagonal entries, i.e. $\varphi_s(bg) = \eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$; for every $s$ and every infinite place $w$ the right translates of $\varphi_s$ by the row-isometry subgroup at $w$ span a finite-dimensional space; every $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; $s \mapsto \varphi_s(g)$ is entire for every $g$; and for each infinite place $w$ there is one finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing $k \mapsto \varphi_s(gk)$ for all $s$ and $g$. Then, with the Borel measurable structure on $\mathbb{A}_F$, there exist a set $O \subseteq \mathbb{C}$ and functions $E^c, N^c \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ such that $O$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re} s = 0\}$ and the half-plane $\{\operatorname{Re} s > 1/2\}$; for each $g$ the functions $s \mapsto E^c_s(g)$ and $s \mapsto N^c_s(g)$ are analytic on a neighbourhood of every point of $O$; $(s,g) \mapsto E^c_s(g)$ and $(s,g) \mapsto N^c_s(g)$ are continuous on $O \times \mathrm{GL}_2(\mathbb{A}_F)$; and for $\operatorname{Re} s > 1/2$ and all $g$ one has $E^c_s(g) = \varphi_s(g) + \sum_{\xi \in F} \varphi_s(w\,n(\xi)\,g)$ and $N^c_s(g) = \int_{\mathbb{A}_F} \varphi_s(w^{-1} n(x) g)\,dx$ against additive adelic Haar measure, where $w$ is the image of the Weyl element in $\mathrm{GL}_2(\mathbb{A}_F)$ and $n(x)$ is the upper unipotent matrix with entry $x$.
--
--   This is the analytic continuation, to a connected open region joining the convergence half-plane $\operatorname{Re} s > 1/2$ to the unitary axis $\operatorname{Re} s = 0$, of the two-cell Bruhat expansion of the $\mathrm{GL}_2$ Eisenstein series attached to an induced family $(\varphi_s)$ and of the global Weyl intertwining integral, with joint continuity in $(s,g)$. It feeds the spectral analysis of pseudo-Eisenstein series and the convolution-operator estimates used later in the trace-formula arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    ∃ (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) := by sorry
