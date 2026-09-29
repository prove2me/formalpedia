-- Prove2me | Theorems.Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
-- name    : AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/814e2245-0c64-5076-b36b-53a23a0f3ad7
-- title:
--   Leading term at s=1/2 unchanged by a local Weyl translation
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the homomorphism from the unit group of the adele ring $\mathbb{A}_F$ to $\mathbb{R}^\times$ obtained from the module (`distribHaarChar`) of the adele ring composed with the inclusion $\mathbb{R}_{\ge 0}\hookrightarrow\mathbb{R}$, assumed pointwise positive via $h\alpha$. Let $\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family subject to: for each $s$, $\varphi_s$ is an induced section for the pair of characters $\alpha^{s+1/2}$ and $\alpha^{-(s+1/2)}$ (with trivial twisting characters $\mu=\nu=1$), i.e. $\varphi_s(bg)=\alpha(b_{11})^{s+1/2}\,\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for every upper triangular $b$; for each $s$ and each infinite place $w$, the right translates of $\varphi_s$ by the subgroup of elements whose $w$-component is a row isometry span a finite-dimensional space; for each $s$, the stabiliser of $\varphi_s$ under right translation by the kernel of the archimedean projection $\mathrm{glArch}$ is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and flatness: $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ lies in $\mathrm{finiteIntegralGL2}$ (integral with integral inverse) and every archimedean component of $k$ is a row isometry. Let $v$ be a finite place of $F$. With the Borel structure and additive Haar measure on $\mathbb{A}_F$, set $M(s)\varphi_s(g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$, where $w$ is the global antidiagonal involution and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then, as $s\to 1/2$ within $\{\operatorname{Re}s>1/2\}$, $(s-\tfrac12)\bigl(M(s)\varphi_s(w_v)-M(s)\varphi_s(1)\bigr)\to 0$, where $w_v$ is the adelic matrix with antidiagonal swap at $v$ and identity at all other places.
--
--   This is the analytic core of the assertion that at $s=1/2$ the global intertwining operator applied to a flat family of sections induced from $(\alpha^{s+1/2},\alpha^{-(s+1/2)})$ has leading term insensitive to translation by the Weyl element at a single finite place, so that the residue is a constant function on the relevant part of the maximal compact subgroup. It is used by [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_mem_maximalCompactAt_singleton), which extends the conclusion from the local Weyl element to arbitrary elements of the local maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family.lean

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
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm.WindowedSiegel Filter Topology
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family
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
      (v : HeightOneSpectrum (𝓞 F)),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    Tendsto (fun s : ℂ => (s - 1 / 2) *
        (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s)
            (AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
          - weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) 1))
      (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 0) := by sorry
