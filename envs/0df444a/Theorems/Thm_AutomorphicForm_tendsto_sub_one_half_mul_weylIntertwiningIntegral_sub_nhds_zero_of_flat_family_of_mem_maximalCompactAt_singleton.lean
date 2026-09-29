-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/41ebe01d-9271-5085-8265-f62ede9d9568
-- title:
--   Leading term at s=1/2 of intertwining integral is Kᵥ-invariant
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the module (distributive Haar character) of the adele ring, viewed as a homomorphism into $\mathbb{R}^\times$, assumed throughout to take positive values. Let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family of functions such that: for each $s$, $\varphi_s$ is a section induced from the adelic Borel subgroup with characters $\alpha^{s+1/2}$ and $\alpha^{-(s+1/2)}$, i.e. $\varphi_s(bg)=\alpha^{s+1/2}(d_1(b))\,\alpha^{-(s+1/2)}(d_2(b))\,\varphi_s(g)$ for all $b$ in the adelic Borel subgroup, where $d_1,d_2$ are its two diagonal entries; each $\varphi_s$ is archimedean $K$-finite at every infinite place and a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and the family is flat, meaning $\varphi_s(k)=\varphi_{s'}(k)$ for all $s,s'$ whenever the finite part of $k$ is integral of level zero and the component of its archimedean part at each infinite place is a row isometry. Let $v$ be a nonzero prime of $\mathcal{O}_F$ and let $k_v \in \mathrm{GL}_2(\mathbb{A}_F)$ lie in the maximal compact subgroup cut out at $\{v\}$, i.e. $k_v$ lies in the adelic maximal compact subgroup (integral finite part, row-isometry archimedean components) and its finite component at every prime other than $v$ is trivial; assume further that the archimedean part of $k_v$ is $1$. Writing $M(s)\varphi_s(g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ for the Weyl intertwining integral against adelic additive Haar measure (the adele ring carrying its Borel structure), the conclusion is that $(s-\tfrac12)\bigl(M(s)\varphi_s(k_v)-M(s)\varphi_s(1)\bigr) \to 0$ as $s \to \tfrac12$ within the half-plane $\{\operatorname{Re} s > \tfrac12\}$.
--
--   This is the finite-place form of the statement that at $s=\tfrac12$ the leading (polar) term of the intertwining operator on the induced representation $\mathrm{Ind}(\alpha^{s+1/2}\otimes\alpha^{-(s+1/2)})$ is constant on the maximal compact subgroup: translation by an element supported at one prime $v$ and integral there changes the intertwining integral by an amount vanishing to higher order. It feeds the corresponding global statement [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_apply_one_nhds_zero_of_flat_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton.lean

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
open AutomorphicForm.WindowedSiegel Filter Topology
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton
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
      (v : HeightOneSpectrum (𝓞 F)) (kv : AdelicGL2 (𝓞 F) F)
      (_hkv : kv ∈ maximalCompactAt F {v}) (_hkv' : glArch (𝓞 F) F kv = 1),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) kv
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
