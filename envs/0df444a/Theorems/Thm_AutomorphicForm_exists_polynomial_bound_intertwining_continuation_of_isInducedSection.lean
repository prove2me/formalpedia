-- Prove2me | Theorems.Thm_AutomorphicForm_exists_polynomial_bound_intertwining_continuation_of_isInducedSection
-- name    : AutomorphicForm.exists_polynomial_bound_intertwining_continuation_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f5dde148-2a11-5ac7-9af4-d2c5b388f31e
-- title:
--   Polynomial vertical bound for the continued intertwining operator
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele units obtained from the distributive Haar character of $\mathbb{A}_F$ by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, assumed pointwise positive ($h\alpha$). Let $\mu,\nu$ be characters of $(\mathbb{A}_F)^\times$ with values in $\mathbb{C}^\times$ which are unitary ($\|\chi(x)\|=1$ for all $x$), trivial on the image of $F^\times$, and continuous. Let $\varphi:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that each $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel, with $\eta_1=\mu\,\alpha^{s+1/2}$ and $\eta_2=\nu\,\alpha^{-(s+1/2)}$; each $\varphi_s$ has finitely many linearly independent right translates under the archimedean row-isometry subgroup at every infinite place, and is a smooth vector for the finite adelic subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous and, for each $g$, entire in $s$; and for each infinite place $w$ a single finite-dimensional space of functions on that isometry subgroup contains every translate $k\mapsto\varphi_s(gk)$, uniformly in $s,g$. Let $Mc$ be such that, for each $g$, $s\mapsto Mc(s)(g)$ is meromorphic in normal form on $\mathbb{C}$ and equals the Weyl intertwining integral $\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ (adelic additive Haar) for $\operatorname{Re} s>1/2$. Then for all $\sigma_0>0$ and $\delta>0$ there are $A\ge 0$ and $N\in\mathbb{N}$ such that for every $s$ with $0\le\operatorname{Re} s\le\sigma_0$ whose distance to $\tfrac12-\tfrac{i\tau}{2}$ is at least $\delta$ for every real $\tau$ with $\mu\nu^{-1}=\|\cdot\|^{i\tau}$, and every $k$ in the adelic maximal compact subgroup, $\|Mc(s)(k)\|\le A(1+|\operatorname{Im} s|)^N\sup_{k'\in\mathbf{K}}\|\varphi_s(k')\|$.
--
--   This is the vertical-strip growth estimate for the meromorphically continued Weyl intertwining operator on a family of induced sections of $\mathrm{GL}_2$ over a number field, in the form in which the possible pole on $\operatorname{Re} s=1/2$ has been excluded by a distance hypothesis rather than regularised by a linear factor. It feeds the contour-shifting and inner-product computations for pseudo-Eisenstein series, being cited in the axis-continuation bound for the intertwining integral and in the decomposition of the pairing of a pseudo-Eisenstein series into a residual projection plus axis integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_polynomial_bound_intertwining_continuation_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
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

theorem AutomorphicForm.exists_polynomial_bound_intertwining_continuation_of_isInducedSection
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
      (σ₀ : ℝ) (_hσ₀ : 0 < σ₀) (δ : ℝ) (_hδ : 0 < δ),
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ →
      (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
          δ ≤ ‖s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)‖) →
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
        ‖Mc s k‖ ≤ A * (1 + |s.im|) ^ N * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖ := by sorry
