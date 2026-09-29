-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
-- name    : AutomorphicForm.exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/69d48a8d-9094-533b-94fe-8df08fdf8ce7
-- title:
--   Equicontinuity of right convolutions on compact sets
-- statement:
--   Let $K$ be a number field, let $\chi$ be a homomorphism from the full unit group $(\mathbb{A}_K^\times$, viewed as the subgroup $\top)$ to $\mathbb{C}^\times$, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a factorizable test function, i.e. $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean factor $f_\infty$ of compact support which is given by a $C^\infty$ function of the matrix entries in the mixed space of $K$, and a locally constant factor $f_{\mathrm{fin}}$ of compact support on $\mathrm{GL}_2$ of the finite adeles. Let $Kc \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be compact, let $\alpha < \beta$ be reals with $0 < \beta$, and let $\Phi_0$ be a measure-theoretic fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ under the diagonal embedding `globalPoints`, for the adelic Haar measure `adelicGLHaar` (for the Borel structure) restricted to the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, where the idele norm is the value of the distributive Haar character of $\mathbb{A}_K$ at $\det g$. Then for every $\varepsilon > 0$ there is a neighbourhood $V$ of $1$ in $\mathrm{GL}_2(\mathbb{A}_K)$ such that for every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfying $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ and $\varphi(z g) = \chi(z)\varphi(g)$ for all central scalars $z \in \mathbb{A}_K^\times$, and lying in $L^2$ of the Haar measure restricted to $\Phi_0$, one has $\|(\varphi * f)(gh) - (\varphi * f)(g)\| \le \varepsilon \, \|\varphi\|_{L^2(\Phi_0)}$ for all $g \in Kc$ and $h \in V$, where $(\varphi * f)(g) = \int \varphi(gx) f(x)\, d\mu(x)$ is the right convolution `rightConv`.
--
--   This is the equicontinuity on compact sets of the family $\{\varphi * f\}$ as $\varphi$ ranges over the unit ball of $L^2(\Phi_0)$ in the space of left $\mathrm{GL}_2(K)$-invariant functions with central character $\chi$; no cuspidality enters. It supplies the Arzelà–Ascoli input for [`AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier`](thm.html#AutomorphicForm.CuspidalSpectrum.isCompactOperator_lift_rightConv_comp_cuspSubcarrier), the compactness of the smoothing operator $R(f)$ on the cuspidal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
  AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_nhds_one_forall_norm_rightConv_mul_sub_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isFundamentalDomain
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    {Kc : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hKc : IsCompact Kc)
    (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 K) K), ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
      IsLsXiFunction (𝓞 K) K ⊤ χ φ → Continuous φ →
        MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) →
          ∀ g ∈ Kc, ∀ h ∈ V,
            ‖rightConv K φ f (g * h) - rightConv K φ f g‖ ≤
              ε * (eLpNorm φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀)).toReal := by sorry
