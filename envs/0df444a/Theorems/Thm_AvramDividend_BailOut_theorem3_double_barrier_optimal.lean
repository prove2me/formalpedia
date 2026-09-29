-- Prove2me | Theorems.Thm_AvramDividend_BailOut_theorem3_double_barrier_optimal
-- name    : AvramDividend.BailOut.theorem3_double_barrier_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:10:05.02406+00:00
-- url     : https://prove2.me/theorems/c53ca6b9-22ac-4bc8-b6b7-008e509442cd
-- title:
--   Theorem 3 — the double-barrier strategy $\bar\pi_{0,d^*}$ is optimal in the bail-out problem
-- statement:
--   Let $X$ be a spectrally negative Lévy process on a filtered probability space satisfying the standing assumptions: no monotone paths, condition (3.3), and $\psi'(0+)=E[X_1]>-\infty$. Let $q>0$ be the discount rate and $\varphi>1$ the cost per unit of injected capital. Let $W^{(q)}$ be the $q$-scale function, $\bar v_a$ the candidate value (5.4), and $d^*$ the barrier level (5.6). Then $d^*<\infty$, and for every initial capital $x\ge0$ the following hold.
--
--   1. The value function of the bail-out problem (2.4) is
--   $$\bar v_*(x)=\bar v_{d^*}(x).$$
--   2. A double-barrier strategy $\bar\pi_{0,d^*}$ from $x$ exists.
--   3. Every double-barrier strategy $\bar\pi_{0,d^*}$ from $x$ is admissible and attains the value: $\bar v_{\bar\pi_{0,d^*}}(x)=\bar v_*(x)$.
--
--   In the bail-out setting the optimal dividend policy is therefore a barrier strategy for every initial capital, with an explicit level and an explicit value in terms of scale functions.
--
--   **Formalization Note** The paper prints the hypothesis as $\psi'(0+)<\infty$, which always holds for a spectrally negative process. The operative hypothesis is $\psi'(0+)>-\infty$ (p. 4, p. 14, Proposition 2), formalized as integrability of $X_1$. The value function is a supremum in the extended reals over admissible policies; policy values are defined in the definition item. $d^*\in[0,\infty]$ is converted to a real number after its finiteness is asserted. When $d^*=0$ (bounded variation only, by Lemma 2(ii)), $\bar v_0$ is (5.5), and the double-barrier strategy at level $0$ is the policy that keeps the risk process at zero.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 15, Theorem 3

import Mathlib
import Definitions.Def_AvramDividend_BailOut_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_BailOut_ScaleFunction
import Definitions.Def_AvramDividend_BailOut_BarrierCandidates
import Definitions.Def_AvramDividend_BailOut_BailOutProblem

open MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.BailOut

theorem theorem3_double_barrier_optimal {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (Lv : SpectrallyNegativeLevy P 𝓕) (hL : Lv.StandingAssumptions)
    {q : ℝ} (hq : 0 < q) {φ : ℝ} (hφ : 1 < φ)
    {W : ℝ → ℝ} (hW : Lv.triplet.IsScaleFunction q W) :
    dStar q φ W < ⊤ ∧
      ∀ x : ℝ, 0 ≤ x →
        optimalValue Lv q φ x = ((vbar Lv q φ W (dStar q φ W).toReal x : ℝ) : EReal) ∧
          (∃ π : Policy Ω, IsDoubleBarrier Lv (dStar q φ W).toReal x π) ∧
          ∀ π : Policy Ω, IsDoubleBarrier Lv (dStar q φ W).toReal x π →
            IsAdmissible Lv q x π ∧ policyValue P q φ π = optimalValue Lv q φ x := by sorry

end AvramDividend.BailOut
