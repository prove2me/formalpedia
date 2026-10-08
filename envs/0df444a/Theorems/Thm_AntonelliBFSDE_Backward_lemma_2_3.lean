-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_lemma_2_3
-- name    : AntonelliBFSDE.Backward.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:21:59.32598+00:00
-- url     : https://prove2.me/theorems/69020067-01b8-4459-aa0d-9c8f39e5f18d
-- title:
--   Lemma 2.3 — the operator $G$ of (2.1) maps $L^1(\mu)$ into $L^1(\mu)$
-- statement:
--   Assume the usual hypotheses, an integrator $A$ with $|A|_T\le\beta$ ($\beta>0$, $T>0$), and hypotheses 1–4 on $g$, $Y$, $k$. Let $V\in L^1(\mu)$. Then:
--
--   1. for every $t\in[0,T]$ the random variable $\xi_t=\int_t^T g_s(V_s)\,dA_s+Y$ is integrable;
--   2. the process $G(V)_t=E(\xi_t\mid\mathcal F_t)$ has a jointly measurable version with càdlàg paths on $[0,T]$;
--   3. every such version belongs to $L^1(\mu)$:
--   $$E\Big(\int_0^T|G(V)_t|\,|dA_t|\Big)<+\infty.$$
--
--   In short, $G:L^1(\mu)\to L^1(\mu)$. This is the first step of the fixed-point argument for Theorem 2.4.
--
--   **Formalization Note** The paper's one-line statement presupposes that $G(V)$ exists as an element of $L^1(\mu)$; items 1 and 2 make this explicit (item 1 is the first line of the paper's proof). The càdlàg requirement on versions is explained in the definition of `IsGVersion`.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 780, Lemma 2.3

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Lemma 2.3 (Antonelli 1993, p. 780): under hypotheses 1–4, for `V ∈ L¹(μ)` every argument
`ξ_t = ∫_t^T g_s(V_s) dA_s + Y` (`t ≤ T`) is integrable, `G(V)_t = E(ξ_t | 𝓕_t)` has a càdlàg
jointly measurable version, and every such version lies in `L¹(μ)`. -/
theorem lemma_2_3 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (T β : ℝ≥0) (hT : 0 < T) (hβ : 0 < β) (I : BVIntegrator 𝓕 T β)
    (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ) (k : ℝ) (hyp : Hypotheses 𝓕 P I g Y k)
    (V : ℝ≥0 → Ω → ℝ) (hV : MemL1 P I V) :
    (∀ t ≤ T, Integrable (xi I g Y V t) P) ∧
      (∃ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P I g Y V W) ∧
      ∀ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P I g Y V W → MemL1 P I W := by sorry

end AntonelliBFSDE.Backward
