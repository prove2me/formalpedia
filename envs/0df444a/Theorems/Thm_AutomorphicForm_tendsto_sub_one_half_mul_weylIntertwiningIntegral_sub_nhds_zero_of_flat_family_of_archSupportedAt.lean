-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/602333c7-35ad-52dc-bc3c-aa6dc0cabe52
-- title:
--   Intertwining residue unchanged by isometry at one archimedean place
-- statement:
--   Let $F$ be a number field, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character of the adele ring of $F$ by composing with the inclusion $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and passing to units, assumed pointwise positive ($h\alpha$). Let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for every $s$, $\varphi_s$ is an induced section for the pair of characters $\alpha^{\,s+1/2}$ and $\alpha^{-(s+1/2)}$ (the `etaFst`/`etaSnd` twists of the trivial character), i.e. $\varphi_s(bg) = \alpha^{\,s+1/2}(b_{11})\,\alpha^{-(s+1/2)}(b_{22})\,\varphi_s(g)$ for all $b$ in the adelic Borel subgroup and all $g$; for every $s$, $\varphi_s$ is archimedean $K$-finite, meaning that at each infinite place the right translates of $\varphi_s$ by the subgroup of row-isometries at that place span a finite-dimensional space; for every $s$, $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; $s \mapsto \varphi_s(g)$ is entire for each $g$; and the family is flat, in the sense that $\varphi_s(k) = \varphi_{s'}(k)$ for all $s,s'$ whenever the finite part of $k$ lies in the level-zero integral subgroup and the component of $k$ at every infinite place is a row isometry (norm-one determinant, and preservation of the sum of squared norms of the two row-combinations). Fix an infinite place $w$ and $k \in \mathrm{GL}_2(\mathbb{A}_F)$ whose finite part is $1$, whose archimedean components at all places $w' \neq w$ are $1$, and whose component at $w$ is a row isometry. Then, with the Borel $\sigma$-algebra and the additive Haar measure on $\mathbb{A}_F$, writing $M(s)\varphi_s(g) = \int_{\mathbb{A}_F} \varphi_s(w_0^{-1} n(x) g)\,dx$ for the Weyl intertwining integral, $$(s - \tfrac12)\bigl(M(s)\varphi_s(k) - M(s)\varphi_s(1)\bigr) \longrightarrow 0$$ as $s \to \tfrac12$ within the half-plane $\{\operatorname{Re} s > \tfrac12\}$.
--
--   This is the statement that the residue at $s = 1/2$ of the constant term of the degenerate Eisenstein family is insensitive to translation of the group variable by an isometry at a single archimedean place; the group-variable independence of the residue in the full maximal compact direction is obtained from it by iterating over the infinite places, in [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_empty).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
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

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt
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
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (_hkw : IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
