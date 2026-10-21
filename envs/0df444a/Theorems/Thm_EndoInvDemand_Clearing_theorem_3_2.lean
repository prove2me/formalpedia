-- Prove2me | Theorems.Thm_EndoInvDemand_Clearing_theorem_3_2
-- name    : EndoInvDemand.Clearing.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:58.782114+00:00
-- url     : https://prove2.me/theorems/7056c08f-20d4-46f9-ab00-f0a0c199444a
-- title:
--   Theorem 3.2, p. 9 — existence of a clearing price (𝔻 = ℝ, or 𝔻 = ℝ₊₊ with H_Z(v₀) ≤ v₀), and compactness of V(Z)
-- statement:
--   Let $R$ satisfy Assumption 3.1 on $\mathbb D\in\{\mathbb R,\mathbb R_{++}\}$, let $\mathcal X$ satisfy Assumption 2.1, and let $Z\in L^\infty$. Write $e=\operatorname{ess\,inf}[\mathcal X+Z]$.
--
--   1. The set of clearing prices is nonempty, $V(Z)\neq\emptyset$, if either $\mathbb D=\mathbb R$, or $\mathbb D=\mathbb R_{++}$ and there is $v_0\in\operatorname{dom}H_Z$ with $H_Z(v_0)\le v_0$.
--   2. If $\mathbb D=\mathbb R_{++}$, such a $v_0$ exists whenever
--   $$e\in\operatorname{dom}H_Z\ \text{and}\ H_Z(e)\le e,\qquad\text{or}\qquad e\notin\operatorname{dom}H_Z\ \text{and}\ \liminf_{v\nearrow e}H_Z(v)<e.$$
--   3. The set $V(Z)$ is compact.
--
--   This is the general existence result for the clearing-price fixed-point problem (3.1); Corollary 3.4 shows that under the uniqueness conditions of Theorem 3.3 the sufficient condition in item 2 is also necessary.
--
--   **Formalization Note** $\liminf_{v\nearrow e}$ is the limit inferior along the left neighbourhood filter of $e$; $H_Z$ is bounded there, so it is a genuine limit inferior. Compactness is unconditional (the empty set is compact).
-- source:
--   Bichuch & Feinstein, Endogenous Inverse Demand Functions, arXiv:2012.08002v3, Theorem 3.2, p. 9

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology

namespace EndoInvDemand.Clearing

/-- Theorem 3.2, p. 9: existence of a clearing price if `𝔻 = ℝ`, or if `𝔻 = ℝ₊₊` and
`H_Z(v₀) ≤ v₀` for some `v₀ ∈ dom H_Z` (which holds under either bullet condition at
`ess inf[𝒳 + Z]`); moreover `V(Z)` is compact. -/
theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ((D = .real ∨ (D = .pos ∧ ∃ v₀ ∈ domH P D R X Z, H P D R X Z v₀ ≤ v₀)) →
        (V P D R X Z).Nonempty) ∧
    (D = .pos →
        ((essInf (fun ω => X ω + Z ω) P) ∈ domH P D R X Z ∧ H P D R X Z (essInf (fun ω => X ω + Z ω) P) ≤ essInf (fun ω => X ω + Z ω) P ∨
          (essInf (fun ω => X ω + Z ω) P) ∉ domH P D R X Z ∧
            Filter.liminf (H P D R X Z) (𝓝[<] (essInf (fun ω => X ω + Z ω) P)) < essInf (fun ω => X ω + Z ω) P) →
        ∃ v₀ ∈ domH P D R X Z, H P D R X Z v₀ ≤ v₀) ∧
    IsCompact (V P D R X Z) := by sorry

end EndoInvDemand.Clearing
