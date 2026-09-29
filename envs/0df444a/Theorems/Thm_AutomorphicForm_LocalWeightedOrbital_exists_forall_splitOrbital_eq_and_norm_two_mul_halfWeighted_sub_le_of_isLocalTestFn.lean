-- Prove2me | Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn
-- name    : AutomorphicForm.LocalWeightedOrbital.exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/5cc79e64-bd2a-54e9-9372-1f86feff70bf
-- title:
--   Logarithmic expansion of half-weighted orbital integrals near t=1
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of $\mathcal{O}_K$ with completion $K_v =$ `v.adicCompletion K` and ring of integers $\mathcal{O}_v$, and let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, i.e. locally constant with compact support. Let $\mu$ be an additive Haar measure on $K_v$ (for the Borel structure) normalised by $\mu(\mathcal{O}_v) = 1$, and let $\mu_K$ denote the Haar measure `localHaar K v` of $\mathrm{GL}_2(K_v)$ — normalised so that the compact open set `localIntegralSet K v` of those $g$ with both $g$ and $g^{-1}$ having entries in $\mathcal{O}_v$ has measure $1$ — restricted to that same set. Write $S(a,b,x) = \int f(\mathtt{arg}\,k\,a\,b\,x)\,d\mu_K(k)$ for the slice attached to $a,b \in K_v^\times$, $O(a,b) = \int_{K_v} S(a,b,x)\,d\mu(x)$ for `splitOrbital`, and, for the norm $\|\cdot\|$ on $K_v$, $H(a,b) = -\sqrt{\|a\|/\|b\|}\int_{\{\,\|1 - b a^{-1}\| < \|x\|\,\}} S(a,b,x)\bigl(\log\|x\| - \log\|1 - b a^{-1}\|\bigr)\,d\mu(x)$ for `halfWeighted`. The assertion is that there exist a real constant $C$ and a neighbourhood $U$ of $1$ in $K_v^\times$ such that for all $a, t \in K_v^\times$ with $t \neq 1$ and $t \in U$ one has $O(a, at) = O(a,a)$ and $$\Bigl\| 2H(a, at) - \Bigl(2\log\|1-t\|\cdot O(a,a) - 2\int_{K_v} S(a,a,x)\log\|x\|\,d\mu(x)\Bigr)\Bigr\| \le C\,\|1-t\|\,\bigl(1 + |\log\|1-t\||\bigr).$$
--
--   This records the local behaviour of Langlands' half-weighted orbital integral as the regular split element $\mathrm{diag}(a,at)$ degenerates to a central one, i.e. as $t \to 1$: near $t = 1$ the split orbital integral does not vary with $t$, and twice the half-weight agrees with $2\log\|1-t\|$ times that orbital integral minus twice the logarithmically weighted slice integral, with error $O(\|1-t\|(1+|\log\|1-t\||))$. It feeds the comparison of weighted orbital integrals at matching local data used in the base-change trace identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalWeightedOrbital_exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalWeightedOrbital.exists_forall_splitOrbital_eq_and_norm_two_mul_halfWeighted_sub_le_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (hμ : μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) = 1) :
    letI := AutomorphicForm.localGLBorel K v
    ∃ C : ℝ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → t ∈ U →
      AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a (a * t) =
        AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a a ∧
      ‖2 * AutomorphicForm.LocalWeightedOrbital.halfWeighted ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ (fun x : v.adicCompletion K => ‖x‖) f a (a * t) -
          (2 * ((Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ : ℝ) : ℂ) *
              AutomorphicForm.LocalWeightedOrbital.splitOrbital ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a a -
            2 * ∫ x : v.adicCompletion K, AutomorphicForm.LocalWeightedOrbital.slice ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) f a a x * ((Real.log ‖x‖ : ℝ) : ℂ) ∂μ)‖ ≤
        C * ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖ * (1 + |Real.log ‖(1 : v.adicCompletion K) - (t : v.adicCompletion K)‖|) := by sorry
