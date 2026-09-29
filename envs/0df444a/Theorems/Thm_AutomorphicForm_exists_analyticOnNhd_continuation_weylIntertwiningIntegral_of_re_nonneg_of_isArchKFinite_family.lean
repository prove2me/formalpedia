-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/c30fe33b-a107-5c63-b3f5-1755228d782d
-- title:
--   Continuation of the GL₂ intertwining integral off one point
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of $\mathbb{A}_F^\times$ obtained from the distributive Haar character of $\mathbb{A}_F$ by viewing its nonnegative real values in $\mathbb{R}^\times$; assume $\alpha$ takes positive values (hypothesis `hα`). Let $\mu,\nu\colon \mathbb{A}_F^\times\to\mathbb{C}^\times$ be monoid homomorphisms which are unitary ($|\mu(x)|=|\nu(x)|=1$ for all ideles $x$), trivial on the image of $F^\times$, and continuous. Let $\varphi\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, written $(s,g)\mapsto\varphi_s(g)$, satisfy: for every $s$, $\varphi_s$ transforms under the adelic Borel subgroup by $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ with $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$ (`etaFst`, `etaSnd`); each $\varphi_s$ is `IsArchKFinite`, i.e. at every infinite place $w$ its right translates under the row-isometry subgroup at $w$ span a finite-dimensional space, and `IsKfSmooth`, i.e. a smooth vector for the finite adelic subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and the archimedean types are uniform in $s$ and $g$: for each infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing $k\mapsto\varphi_s(gk)$ for all $s$ and $g$. Then, with the Borel $\sigma$-algebra on $\mathbb{A}_F$, there exist $c\in\mathbb{C}$ with $\operatorname{Re}c=1/2$, an open $U\subseteq\mathbb{C}$ with $\{s:\operatorname{Re}s\ge 0\}\setminus\{c\}\subseteq U$, and $N\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that $s\mapsto N(s,g)$ is analytic on a neighbourhood of each point of $U$ for every $g$, $(s,g)\mapsto N(s,g)$ is continuous on $U\times\mathrm{GL}_2(\mathbb{A}_F)$, and for $\operatorname{Re}s>1/2$ and all $g$ one has $N(s,g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$, the Weyl intertwining integral of $\varphi_s$ against the additive adelic Haar measure.
--
--   This is the constant-term half of the holomorphy of the $\mathrm{GL}_2$ Eisenstein family on and to the right of the unitary axis: the constant term along the unipotent radical is built from $\varphi_s$ together with the intertwining integral $M(\varphi_s)$, and the single excluded point $c$ on the line $\operatorname{Re}s=1/2$ accounts for the residual pole. It feeds the continuation statement for the Bruhat form of the Eisenstein family and the inner-product computation for such continuations at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.exists_analyticOnNhd_continuation_weylIntertwiningIntegral_of_re_nonneg_of_isArchKFinite_family
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
    ∃ (c : ℂ) (U : Set ℂ) (Nc : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      c.re = 1 / 2 ∧ IsOpen U ∧ {s : ℂ | 0 ≤ s.re} \ {c} ⊆ U ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nc s g) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nc p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g) := by sorry
