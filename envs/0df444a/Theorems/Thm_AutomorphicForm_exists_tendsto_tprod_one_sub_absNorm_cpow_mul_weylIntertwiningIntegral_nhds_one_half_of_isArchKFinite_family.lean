-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/4ea1e08a-eb0f-5a62-9438-67862a2be3ef
-- title:
--   Non-zero g-independent limit of the normalised intertwining integral
-- statement:
--   Let $F$ be a number field and let $\alpha\colon (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group homomorphism obtained from the module character `distribHaarChar` of the adele ring of $F$ followed by the inclusion $\mathbb{R}_{\ge 0}\hookrightarrow\mathbb{R}$, with $h\alpha$ the hypothesis that $\alpha(t)>0$ for all $t$. Let $\varphi\colon \mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that: for each $s$, $\varphi_s$ is an induced section for the pair of characters `etaFst 1 α hα s` $=\alpha^{s+1/2}$ and `etaSnd 1 α hα s` $=\alpha^{-(s+1/2)}$, i.e. $\varphi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi_s(g)$ for every $b$ in `adelicBorel` and every $g$; for each $s$ and each infinite place $w$ of $F$ the right translates of $\varphi_s$ under the subgroup `archRowIsometrySubgroup F w` span a finite-dimensional space (`IsArchKFinite`); for each $s$, $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$-subgroup (`IsKfSmooth`); $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; and $s\mapsto\varphi_s(g)$ is entire for each $g$. Equip the adele ring with its Borel $\sigma$-algebra and let $M(s)\varphi_s(g)=\int_{\mathbb{A}_F}\varphi_s(w^{-1}n(x)g)\,dx$ be `weylIntertwiningIntegral` taken against the additive Haar measure `adelicAddHaar`. The assertion is that there is a finite set $S_0$ of height-one primes of $\mathcal{O}_F$ such that for every finite $S\supseteq S_0$ there exists $\rho\in\mathbb{C}$ with, first, for *every* $g\in \mathrm{GL}_2(\mathbb{A}_F)$,
--   $$\Bigl(\textstyle\prod_{v\notin S}\bigl(1-N(v)^{-2s}\bigr)\Bigr)\,M(s)\varphi_s(g)\longrightarrow \rho \qquad (s\to\tfrac12 \text{ within } \{\operatorname{Re} s>\tfrac12\}),$$
--   the same $\rho$ for all $g$; and, second, $\rho\neq 0$ provided both: $\varphi_{1/2}(k)$ is real and non-negative for every $k$ whose finite part `glFin` lies in `finiteIntegralGL2 (𝓞 F) F` and whose archimedean component at each infinite place $w$ satisfies `IsRowIsometry` (the determinant has absolute value $1$ and $\|xk_{00}+yk_{10}\|^2+\|xk_{01}+yk_{11}\|^2=\|x\|^2+\|y\|^2$ for all $x,y$); and $\varphi_{1/2}(k)\neq 0$ for at least one such $k$.
--
--   This is the residue statement for the global intertwining operator attached to the degenerate principal series family $\mathrm{Ind}(\alpha^{s+1/2},\alpha^{-(s+1/2)})$ at the reducibility point $s=1/2$: after removal of the partial Euler product $\prod_{v\notin S}(1-N(v)^{-2s})$ the operator has a finite limit which is a constant function of the group variable, and the limit is non-zero for a non-negative section not vanishing identically on the maximal compact subgroup. It feeds the meromorphic continuation of the Bruhat-cell Eisenstein term, via [`AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family.lean

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

theorem AutomorphicForm.exists_tendsto_tprod_one_sub_absNorm_cpow_mul_weylIntertwiningIntegral_nhds_one_half_of_isArchKFinite_family
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
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
      ∃ ρ : ℂ,
      (∀ g : AdelicGL2 (𝓞 F) F,
        Tendsto (fun s : ℂ =>
            (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))) *
              weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g)
          (𝓝[{s : ℂ | 1 / 2 < s.re}] (1 / 2 : ℂ)) (𝓝 ρ)) ∧
      ((∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) →
        (∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0) →
        ρ ≠ 0) := by sorry
