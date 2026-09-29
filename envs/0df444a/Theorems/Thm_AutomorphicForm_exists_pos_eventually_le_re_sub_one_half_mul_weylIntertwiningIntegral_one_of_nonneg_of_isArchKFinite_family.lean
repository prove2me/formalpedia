-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3cabe853-73b3-52fd-9a5a-73c410ded5a7
-- title:
--   Positive lower bound for (σ-tfrac12)M(σ)φ_σ(1)
-- statement:
--   Let $F$ be a number field and let $\alpha\colon(\mathbb{A}_F)^\times\to\mathbb{R}^\times$ be the character of units obtained from the module character `distribHaarChar` of the adele ring of $F$ composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$, assumed (hypothesis $h\alpha$) to take strictly positive values. Let $\varphi\colon\mathbb{C}\to(\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C})$ be a family such that for every $s$: $\varphi_s$ transforms under the adelic Borel subgroup by $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ with $\chi_1=\alpha^{s+1/2}$, $\chi_2=\alpha^{-(s+1/2)}$ (in the `cpowChar` sense, the inducing characters `etaFst 1 α hα s` and `etaSnd 1 α hα s`); at each infinite place $w$ the right translates of $\varphi_s$ by the archimedean row-isometry subgroup at $w$ span a finite-dimensional space; and $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup. Assume further that $(s,g)\mapsto\varphi_s(g)$ is jointly continuous, that $s\mapsto\varphi_s(g)$ is entire for each $g$, that $\varphi_{1/2}(k)$ is real and $\ge 0$ for every $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ is a row isometry (unit determinant norm and preservation of the sum of squared norms of the two coordinates of a row vector), and that $\varphi_{1/2}(k)\neq0$ for at least one such $k$. Then there exists $\delta>0$ such that for all real $\sigma$ in some right neighbourhood filter of $1/2$, $\delta\le\operatorname{Re}\bigl((\sigma-\tfrac12)\int_{\mathbb{A}_F}\varphi_\sigma(w^{-1}n(x))\,dx\bigr)$, the integral being the Weyl intertwining integral at the identity taken against the adelic additive Haar measure.
--
--   This is the positivity half of the statement that the residue at $s=1/2$ of the intertwining operator applied to an induced section is a positive multiple of $\int_K\varphi_{1/2}(k)\,dk$, stated only at the identity and along real parameters approaching $1/2$ from above. It feeds the analysis of the Euler-product form of the intertwining integral near $s=1/2$ in [`AutomorphicForm.exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family
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
      (_hpos : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0)
      (_hex : ∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        δ ≤ (((σ : ℂ) - 1 / 2) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by sorry
