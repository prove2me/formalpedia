-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
-- name    : AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/cab05e43-4ba5-597b-ace4-e6f8e01f84e2
-- title:
--   Adelic Weyl intertwining integral has a simple pole at σ=1/2
-- statement:
--   Let $F$ be a number field, let $S_1$ be a finite set of finite places of $F$ (nonzero primes of $\mathcal O_F$), let $U$ assign to each finite place $v$ a subset $U_v$ of the completion $F_v$, subject to the requirement that $U_v$ be open and nonempty for $v\in S_1$ (no condition is imposed for $v\notin S_1$), and let $U_0$ be an open nonempty subset of the infinite adele ring $F_\infty$. The adele ring $\mathbb A_F$ carries its Borel $\sigma$-algebra and the additive Haar measure `adelicAddHaar`. Then there are real numbers $m_0,m_1$ with $m_0>0$ such that, for all real $\sigma$ in some right neighbourhood of $1/2$ (i.e. eventually along the filter $\mathcal N[>](1/2)$), one has both
--   $$m_0 \le (\sigma-\tfrac12)\int_{\{x\,:\,x_\infty\in U_0,\ x_v\in U_v\ (v\in S_1)\}} H\big(w^{-1}n(x)\big)^{\sigma+\frac12}\,dx,\qquad (\sigma-\tfrac12)\int_{\mathbb A_F} H\big(w^{-1}n(x)\big)^{\sigma+\frac12}\,dx \le m_1 .$$
--   Here $n(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ in $\mathrm{GL}_2(\mathbb A_F)$, $w$ is the image in $\mathrm{GL}_2(\mathbb A_F)$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $F$ under the entrywise structure map, the exponentiation is real rpow, and $H=$ `adelicHeight` is the product of the archimedean height $\prod_{v\mid\infty}\mathrm{localHeight}(g_v)^{\mathrm{mult}(v)}$ of the archimedean component with the finite height $\prod^{\mathrm{f}}_{v}\mathrm{finLocalHeight}(g_v)$ of the finite component. The integration domain of the first integral is the cylinder set of adeles whose infinite part lies in $U_0$ and whose $v$-component lies in $U_v$ for all $v\in S_1$.
--
--   This is the quantitative form, over the adeles of a number field, of the Gindikin–Karpelevich/Langlands evaluation of the spherical intertwining integral for $\mathrm{GL}_2$: the integral of $H(w^{-1}n(x))^{\sigma+1/2}$ has a simple pole at $\sigma=1/2$, and an arbitrary nonempty cylinder set already contributes a positive proportion of its residue. It feeds the lower bound for the Weyl intertwining integral used in the analytic input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow.lean

import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm Filter Topology

theorem AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
    (F : Type) [Field F] [NumberField F]
    (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F))
    (hU : ∀ v ∈ S₁, IsOpen (U v) ∧ (U v).Nonempty)
    (U₀ : Set (InfiniteAdeleRing F)) (hU₀ : IsOpen U₀ ∧ U₀.Nonempty) :
    letI := adeleBorel (𝓞 F) F
    ∃ m₀ m₁ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        m₀ ≤ (σ - 1 / 2) *
            ∫ x in {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v},
              adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ∧
        (σ - 1 / 2) *
            ∫ x, adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ≤ m₁ := by sorry
