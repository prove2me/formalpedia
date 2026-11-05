-- Prove2me | Theorems.Thm_BauerleRiederMDP_PDMDP_theorem_8_3_3
-- name    : BauerleRiederMDP.PDMDP.theorem_8_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:02.460177+00:00
-- url     : https://prove2.me/theorems/4dd91e28-39c5-4eb3-8e9f-82677d1ce7ce
-- title:
--   Theorem 8.3.3 — the finite-horizon chain: $V$ is a fixed point of $T$ and a time-dependent maximizer is optimal
-- statement:
--   Let a continuous-time Markov Decision Chain with finite time horizon $T$ and terminal reward $g$ be given. Suppose that it has an upper bounding function $b$ and that the assumptions (i)–(iv) of Theorem 8.3.1 hold. Write $E'=[0,T]\times E$. Then there exists an optimal Markov policy $\pi^*_t=f^*(t,X_{t-})$, $t\in[0,T]$, for a decision rule $f^*:E'\to U$, where $f^*(t,x)$ is a maximum point of
--   $$
--   u\mapsto r(x,u)+\sum_{y\in E}q_{xy}(u)V(t,y).
--   $$
--   Moreover $V$ is a fixed point of the operator $T$ in $\mathbb B_b^+$, that is,
--   $$
--   V(t,x)=e^{-\lambda(T-t)}g(x)+\int_0^{T-t}e^{-\lambda s}\sup_{u\in U}\Big[r(x,u)+\lambda\sum_{y\in E}V(t+s,y)Q(\{y\}|x,u)\Big]\,ds.
--   $$
--
--   No condition $\alpha_b<1$ is needed: the finite horizon supplies the contraction. This is the form in which the chain is used in applications in finance and insurance.
--
--   **Formalization Note** $V$ is the continuous-time value of (8.12), a supremum over all Markov policies $f_n:[0,T]\times E\to A$. The optimal policy is the one with $f_n(t,x)(s)=f^*(t+s,x)$ for every $n$, as in the proof.
--
--   Differences from the source:
--   - encoding: U is a compact Borel subset of a Polish space → U is a nonempty compact metrizable space with its Borel σ-algebra; reason: a compact subset of a Polish space is exactly a compact metrizable space; every theorem here has U compact, and an empty U has no controls, so the book’s action sets are nonempty
--   - encoding: value functions in [-∞, ∞) → EReal values, with integrals taken as the difference of the Lebesgue integrals of the positive and the negative part; reason: the bounding function makes the positive parts finite, so no ∞ - ∞ occurs
--   - encoding: the maximum-point property at every (t, x) ∈ E′ → the maximum-point property at every (t, x) ∈ E′ with V(t, x) > -∞; reason: at V(t, x) = -∞ the term q_{xx}(u)V(t, x) makes the display of the form ∞ - ∞
--   - encoding: V ∈ IB_b^+ for the bounding function e^{γ(T-t)} b(x) of p.260 → V⁺(t, x) ≤ c b(x) on E′, which is γ = 0; reason: all these classes coincide, since e^{γ(T-t)} lies between 1 and e^{γT}
--   - encoding: f* : E′ → U and f_n : [0, T] × E → A → measurable maps on ℝ × E and jointly measurable rules on ℝ × (ℝ × E), read on E′; reason: every map on [0, T] extends measurably, and only the values on E′ enter; U is nonempty
--   - encoding: rates q_{xy}(u) ∈ ℝ → q_{xy}(u) ≥ 0 for y ≠ x and q_{xy} measurable in u; reason: these make Q a stochastic kernel, which the book’s construction requires
--   - encoding: E countable → E countable with the discrete topology and σ-algebra; reason: the standard structure of a countable state space
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.3.3, p.261

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_FiniteChain
import Definitions.Def_MDPFinance_PDMDP_Core

open MDPFinance.PDMDP (IBbPlus)

namespace BauerleRiederMDP.PDMDP

/-- Theorem 8.3.3 (Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), p.261, PDF 272). Suppose the continuous-time Markov Decision Chain has an
upper bounding function `b` and the continuity and compactness assumptions (i)–(iv) of Theorem
8.3.1 are satisfied. Then there exists an optimal Markov policy `π*_t = f*(t, X_{t-})`,
`t ∈ [0,T]`, for a decision rule `f* : E' → U`, where `f*(t,x)` is a maximum point of
`u ↦ r(x,u) + ∑_y q_{xy}(u) V(t,y)`. Moreover `V(t,x)` is a fixed point of `T` in `IB_b^+`, i.e.
`V(t,x) = e^{-λ(T-t)} g(x) + ∫_0^{T-t} e^{-λs} sup_u [r(x,u) + λ ∑_y V(t+s,y) Q({y}|x,u)] ds`.

**Formalization Note** `E' = [0,T] × E`. The class `IB_b^+` on `E'` is taken for the bounding
function `e^{γ(T-t)} b(x)` at `γ = 0`, the smallest of these classes (they all coincide, since
`e^{γ(T-t)}` lies between `1` and `e^{γT}`). `f*` is a measurable map on `ℝ × E`, read on `E'`.
The maximum-point property is stated where `V(t,x) > -∞`, as in Theorem 8.3.1. -/
theorem theorem_8_3_3 {E U : Type*} [TopologicalSpace E] [DiscreteTopology E] [Countable E]
    [MeasurableSpace E] [BorelSpace E] [TopologicalSpace U] [TopologicalSpace.MetrizableSpace U]
    [MeasurableSpace U] [BorelSpace U] [Nonempty U] (C : FiniteChain E U) (b : E → ℝ)
    (hb : C.IsUpperBounding b) (hcc : C.toRateModel.ContinuityCompactness b) :
    (∃ (fs : ℝ × E → U) (hfs : Measurable fs),
        (∀ t ∈ Set.Icc 0 C.horizon, ∀ x, C.V t x ≠ ⊥ →
          ∀ u, C.rateObjective (C.V t) x u ≤ C.rateObjective (C.V t) x (fs (t, x))) ∧
        ∀ t ∈ Set.Icc 0 C.horizon, ∀ x, C.Vpi (fun _ => timedRule fs hfs) t x = C.V t x) ∧
      (fun p : Set.Icc 0 C.horizon × E => C.V p.1 p.2) ∈ IBbPlus (fun p => b p.2) ∧
      ∀ t ∈ Set.Icc 0 C.horizon, ∀ x, C.V t x = C.T C.V t x := by sorry

end BauerleRiederMDP.PDMDP
