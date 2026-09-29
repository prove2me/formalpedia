-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/13100117-dbc7-5327-a545-b02e2fd8899b
-- title:
--   Flat families: intertwining integral residue independent of K-variable
-- statement:
--   Let $F$ be a number field, and let $\alpha\colon \mathbb{A}_F^\times\to\mathbb{R}^\times$ be the character obtained from the module (distributive Haar) character of the adele ring of $F$ by composing with the inclusion $\mathbb{R}_{\ge 0}\hookrightarrow\mathbb{R}$ and passing to units, and let $h\alpha$ be the hypothesis that $\alpha(t)>0$ for all $t$. Let $\varphi\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family subject to: for each $s$, $\varphi_s$ is an induced section for the pair of characters $\mathrm{etaFst}\,1\,\alpha\,h\alpha\,s=\alpha^{s+1/2}$ and $\mathrm{etaSnd}\,1\,\alpha\,h\alpha\,s=\alpha^{-(s+1/2)}$, that is $\varphi_s(bg)=\alpha^{s+1/2}(b_{11})\,\alpha^{-(s+1/2)}(b_{22})\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero) and all $g$; for each $s$ and each infinite place $w$ the right translates of $\varphi_s$ under the subgroup of row isometries at $w$ span a finite-dimensional space; each $\varphi_s$ is a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; $s\mapsto\varphi_s(g)$ is entire for every $g$; and the family is flat, in the sense that $\varphi_s(k)=\varphi_{s'}(k)$ for all $s,s'$ whenever the finite part of $k$ lies in $\mathrm{finiteIntegralGL2}$ and, at every infinite place $w$, the component $k_w$ satisfies $\mathrm{IsRowIsometry}$, i.e. $\|\det k_w\|=1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y$. Write $M(s)\varphi_s(g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ for the Weyl intertwining integral against the additive Haar measure on the adeles, the adeles being given their Borel $\sigma$-algebra. Then for every $k$ with finite part in $\mathrm{finiteIntegralGL2}$ and all archimedean components row isometries, $(s-\tfrac12)\bigl(M(s)\varphi_s(k)-M(s)\varphi_s(1)\bigr)\to 0$ as $s\to\tfrac12$ within the half-plane $\{\operatorname{Re} s>\tfrac12\}$.
--
--   This is the statement, for flat sections, that the leading (simple-pole) term of the intertwining operator at the point $s=1/2$ where the Eisenstein series of the principal series $\alpha^{s+1/2}\otimes\alpha^{-(s+1/2)}$ has its residue does not depend on the variable within the maximal compact subgroup. It feeds the corresponding statement for arbitrary elements of the adelic maximal compact subgroup, [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_mem_maximalCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family.lean

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
open AutomorphicForm.WindowedSiegel Filter Topology
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family
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
          φ s k = φ s' k),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      Tendsto (fun s : ℂ => (s - 1 / 2) *
          (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) k
            - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
        (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
