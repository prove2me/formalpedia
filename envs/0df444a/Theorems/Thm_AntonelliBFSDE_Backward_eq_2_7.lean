-- Prove2me | Theorems.Thm_AntonelliBFSDE_Backward_eq_2_7
-- name    : AntonelliBFSDE.Backward.eq_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:22:12.066673+00:00
-- url     : https://prove2.me/theorems/f082b4ee-3a20-4f03-9f05-fe7ea7f4f817
-- title:
--   (2.7) — pointwise bound $|G^{(n)}(U)_t-G^{(n)}(V)_t|\le k^nE(\int_t^T(A_{s-}-A_t)^{[n-1]}|U_s-V_s|dA_s\mid\mathcal F_t)$
-- statement:
--   Assume the usual hypotheses, hypotheses 1–4, and that the integrator $A$ is nondecreasing ($A=|A|$, $A^-\equiv0$). Let $U,V\in L^1(\mu)$, and let $G^{(n)}(U)$, $G^{(n)}(V)$ denote the Picard iterates, i.e. sequences of processes with $G^{(0)}(U)=U$ and $G^{(j+1)}(U)$ a (càdlàg) version of $G(G^{(j)}(U))$, and likewise for $V$. Then for every $n\ge1$ and $t\in[0,T]$, $P$-almost surely,
--   $$|G^{(n)}(U)_t-G^{(n)}(V)_t|\le k^n\,E\Big(\int_t^T(A_{s-}-A_t)^{[n-1]}\,|U_s-V_s|\,dA_s\ \Big|\ \mathcal F_t\Big),$$
--   where the integral is over $(t,T]$ and $(A_{s-}-A_t)^{[n-1]}=\sum_{i=0}^{n-1}(-1)^iA_{s-}^{((n-1-i)-)}A_t^{(i)}$.
--
--   This is the pointwise half of the induction in the proof of Theorem 2.4.
--
--   **Formalization Note** The proof of Theorem 2.4 reduces to nondecreasing $A$ ("without loss of generality"), so this step takes $A$ nondecreasing. As on the page, $U$ and $V$ are any elements of $L^1(\mu)$, adapted or not. Iterates are given as chains of versions, since $G$ is defined only up to versions.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 781, (2.7), in the proof of Theorem 2.4

import Mathlib
import Definitions.Def_AntonelliBFSDE_Backward_Setting
import Definitions.Def_AntonelliBFSDE_Backward_Equation

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace AntonelliBFSDE.Backward

/-- (2.7), proof of Theorem 2.4, p. 781 (`A` nondecreasing, any `U, V ∈ L¹(μ)`): for chains of
Picard iterates `G^{(n)}(U) = Uᵢ n`, `G^{(n)}(V) = Vᵢ n`, every `n ≥ 1` and `t ≤ T`,
`|G^{(n)}(U)_t - G^{(n)}(V)_t| ≤ k^n E(∫_t^T (A_{s-} - A_t)^{[n-1]} |U_s - V_s| dA_s | 𝓕_t)` a.s. -/
theorem eq_2_7 {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (hUH : UsualHypotheses 𝓕 P)
    (T β : ℝ≥0) (hT : 0 < T) (hβ : 0 < β) (I : BVIntegrator 𝓕 T β)
    (hA_incr : ∀ t ω, I.Aneg t ω = 0)
    (g : ℝ≥0 → Ω → ℝ → ℝ) (Y : Ω → ℝ) (k : ℝ) (hyp : Hypotheses 𝓕 P I g Y k)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1 P I U) (hV : MemL1 P I V)
    (Uᵢ Vᵢ : ℕ → ℝ≥0 → Ω → ℝ) (hU₀ : Uᵢ 0 = U) (hV₀ : Vᵢ 0 = V)
    (hUᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Uᵢ j) (Uᵢ (j + 1)))
    (hVᵢ : ∀ j, IsGVersion 𝓕 P I g Y (Vᵢ j) (Vᵢ (j + 1)))
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0) (ht : t ≤ T) :
    (fun ω => |Uᵢ n t ω - Vᵢ n t ω|) ≤ᵐ[P] fun ω =>
      k ^ n * MeasureTheory.condExp (𝓕 t) P
        (fun ω' => ∫ s in Set.Ioc (t : ℝ) T,
          bracketLeft (fun r => I.A r ω') (n - 1) s.toNNReal t *
            |U s.toNNReal ω' - V s.toNNReal ω'| ∂I.posMeasure ω') ω := by sorry

end AntonelliBFSDE.Backward
