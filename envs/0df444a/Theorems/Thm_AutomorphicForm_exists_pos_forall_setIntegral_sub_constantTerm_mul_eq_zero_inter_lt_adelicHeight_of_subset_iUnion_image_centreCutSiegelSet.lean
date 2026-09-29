-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet
-- name    : AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/bc55c7e8-0dbd-525a-aeb9-6fe0dc30404f
-- title:
--   Vanishing of the truncated constant-term defect integral
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A}_K$ and $\mathrm{GL}_2(\mathbb{A}_K)$ carrying its Borel $\sigma$-algebra and Haar measure `adelicGLHaar`. Let $\alpha,\beta,c,u,d_1,d_2$ be real numbers with $c>0$, let $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ be compact, and let $\Phi_0\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ satisfy three hypotheses: $\Phi_0$ is contained in $\bigcup_{y\in T_c}\mathfrak{S}\,y$, where $\mathfrak{S}$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$, consisting of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at each infinite place $w$ has local height $\lVert\det\rVert/\mathrm{rowNormSq}$ at least $c$, window quantity `xWindowSq` at most $u^2$, and $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$; $\Phi_0$ lies in the determinant slab $\{g:\ \lVert\det g\rVert_{\mathbb{A}_K}\in[\alpha,\beta]\}$, the idele norm being the distributive Haar character of $\mathbb{A}_K$; and $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$ on Haar measure restricted to that slab. Then there exists $T_0>0$ such that for every $T\ge T_0$ and all measurable $a,d:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $a$ and $d$ invariant under left translation by the image of the rational upper-triangular subgroup $\{\gamma:\gamma_{10}=0\}$ and $d$ invariant under left translation by all $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb{A}_K$: if $\bigl(a-a_N\bigr)\,d$ is integrable on $\Phi_0\cap\{g:\ \mathrm{adelicHeight}(g)>T\}$, where $a_N(g)=\int a\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\bigr)\,dx$ against additive adelic Haar measure conditioned on the adelic box (a probability measure), then $\int_{\Phi_0\cap\{\mathrm{adelicHeight}>T\}}\bigl(a(g)-a_N(g)\bigr)d(g)\,dg=0$. Here $\mathrm{adelicHeight}$ is the product of the archimedean and finite heights of the corresponding components.
--
--   This is the adelic $\mathrm{GL}_2$ form of Arthur's basic truncation lemma: above a sufficiently high height cut-off the defect $a-a_N$ of a Borel-invariant function pairs to zero against any function invariant under the rational Borel subgroup and under $N(\mathbb{A}_K)$, here stated for an arbitrary fundamental domain covered by finitely many compactly-translated centre-cut Siegel sets rather than for one canonical domain. It is used in the assembly of the truncated geometric side, being cited by [`AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero`](thm.html#AutomorphicForm.exists_forall_integrableOn_indicator_mul_setIntegral_finsum_borel_sigmaConjClassOrbit_sub_setIntegral_constantTerm_and_setIntegral_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_inter_lt_adelicHeight_of_subset_iUnion_image_centreCutSiegelSet
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)) (hTc : IsCompact Tc)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet K c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a d : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable d →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          a (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          d (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = d g) →
        (∀ (x : AdeleRing (𝓞 K) K) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K),
          d (AutomorphicForm.unipotentGL2 x * g) = d g) →
        IntegrableOn
          (fun g => (a g - AutomorphicForm.constantTerm
              (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g)
          (Φ₀ ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g}) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in Φ₀ ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g},
            (a g - AutomorphicForm.constantTerm
                (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
