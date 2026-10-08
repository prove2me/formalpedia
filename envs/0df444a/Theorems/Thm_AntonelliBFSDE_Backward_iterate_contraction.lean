-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_iterate_contraction
-- name    : AntonelliBFSDE.Backward.iterate_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:27.910143+00:00
-- url     : https://prove2.me/theorems/62a1e109-2da4-48c5-890d-23ac6fd721e4
-- title:
--   Proof of Theorem 2.4, p. 783 — $\|G^{(n)}(U)-G^{(n)}(V)\|_{L^1(\mu)}\le k^n(\beta^n/n!)\|U-V\|_{L^1(\mu)}$
-- statement:
--   Assume the usual hypotheses, hypotheses 1–4 with $|A|_T\le\beta$, and $A$ nondecreasing. Let $U,V\in L^1(\mu)$, with chains of Picard iterates $G^{(n)}(U)$, $G^{(n)}(V)$ (each a càdlàg version of $G$ applied to the previous one). Then for every $n\ge0$,
--   $$\|G^{(n)}(U)-G^{(n)}(V)\|_{L^1(\mu)}\le k^n\,\frac{\beta^n}{n!}\,\|U-V\|_{L^1(\mu)}.$$
--   Since $k^n\beta^n/n!\to0$, some iterate $G^{(n)}$ is a contraction of $L^1(\mu)$; the Banach fixed point theorem then yields Theorem 2.4.
--
--   **Formalization Note** The paper prints the left side as $\|G(U)-G(V)\|_{L^1(\mu)}$; the surrounding text (the bound for $G^{(n)}$ obtained from (2.8), and "for $n$ sufficiently large, $G^{(n)}$ is a contraction") shows that $G^{(n)}$ is meant, and that is what is stated. Norms are in $[0,\infty]$. The reduction to nondecreasing $A$ is as in (2.7); $U,V$ range over all of $L^1(\mu)$, as on the page.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 783, proof of Theorem 2.4 (display after A^(n−) ≤ A^n/n!)

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- Proof of Theorem 2.4, p. 783 (`A` nondecreasing, any `U, V ∈ L¹(μ)`): the `n`-th Picard
iterate satisfies `‖G^{(n)}(U) - G^{(n)}(V)‖_{L¹(μ)} ≤ k^n (β^n / n!) ‖U - V‖_{L¹(μ)}`. -/
theorem iterate_contraction {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (T β : ℝ≥0) (hT : 0 < T) (hβ : 0 < β) (I : BVIntegrator 𝓕 T β)
    (hA_incr : ∀ t ω, I.Aneg t ω = 0)
    (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ) (k : ℝ) (hyp : Hypotheses 𝓕 P I g Y k)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1 P I U) (hV : MemL1 P I V)
    (Uᵢ Vᵢ : ℕ → ℝ≥0 → Ω → ℝ) (hU₀ : Uᵢ 0 = U) (hV₀ : Vᵢ 0 = V)
    (hUᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Uᵢ j) (Uᵢ (j + 1)))
    (hVᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Vᵢ j) (Vᵢ (j + 1)))
    (n : ℕ) :
    L1Norm P I (fun s ω => Uᵢ n s ω - Vᵢ n s ω) ≤
      ENNReal.ofReal (k ^ n * (β : ℝ) ^ n / (n.factorial : ℝ)) *
        L1Norm P I (fun s ω => U s ω - V s ω) := by sorry

end AntonelliBFSDE.Backward
