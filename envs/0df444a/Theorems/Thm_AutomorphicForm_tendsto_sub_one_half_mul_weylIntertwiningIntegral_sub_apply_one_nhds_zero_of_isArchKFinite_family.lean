-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b9859d4a-6dd6-50c1-b381-2acc888bd1d9
-- title:
--   Leading term at s=1/2 of the Weyl intertwining integral is g-independent
-- statement:
--   Let $F$ be a number field and let $\alpha \colon (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the homomorphism of unit groups obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ composed with the coercion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ (the idelic modulus), assumed to take positive values, this positivity being the hypothesis $h\alpha$. Let $\varphi \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for every $s$, $\varphi_s$ satisfies the induction law $\varphi_s(bg) = \alpha(b_{11})^{s+1/2}\,\alpha(b_{22})^{-(s+1/2)}\,\varphi_s(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (the matrices with vanishing lower-left entry), the exponentials being complex powers of the positive reals $\alpha(b_{11})$, $\alpha(b_{22})$ and the characters $\mu,\nu$ being trivial; for every $s$ and every infinite place $w$ of $F$, the right translates of $\varphi_s$ under the subgroup `archRowIsometrySubgroup F w` span a finite-dimensional space; for every $s$, $\varphi_s$ is a smooth vector for right translation by the kernel of the archimedean projection `glArch`; the map $(s,g) \mapsto \varphi_s(g)$ is continuous; and for each $g$ the map $s \mapsto \varphi_s(g)$ is differentiable on all of $\mathbb{C}$. Write $M(s)\varphi_s(g) = \int_{\mathbb{A}_F} \varphi_s\!\left(w^{-1} \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix} g\right) dx$ for the Weyl intertwining integral, taken against the additive Haar measure on $\mathbb{A}_F$ with its Borel structure, $w$ being the adelic Weyl element. Then for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$, $(s-\tfrac12)\bigl(M(s)\varphi_s(g) - M(s)\varphi_s(1)\bigr) \to 0$ as $s \to \tfrac12$ within the half-plane $\{\operatorname{Re} s > \tfrac12\}$.
--
--   This expresses, for the degenerate principal series family on $\mathrm{GL}_2$ over a number field, that the intertwining integral has at worst a simple pole at $s = 1/2$ whose leading coefficient is independent of the group variable — classically, that at $s = 1/2$ the intertwining operator carries the induced representation onto the constants. It feeds into the analysis of the intertwining integral near $s = 1/2$ via the Gindikin–Karpelevich expression in terms of partial Dedekind zeta factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_isArchKFinite_family
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
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∀ g : AdelicGL2 (𝓞 F) F,
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
