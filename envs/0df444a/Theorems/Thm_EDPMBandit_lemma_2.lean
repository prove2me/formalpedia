-- Prove2me | Theorems.Thm_EDPMBandit_lemma_2
-- name    : EDPMBandit.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:10.679412+00:00
-- url     : https://prove2.me/theorems/565d4a07-0638-42e0-984e-21469e904c82
-- title:
--   Lemma 2 — tail bound for the empirical distribution of any policy
-- statement:
--   Assume Requirement 2 of stability with parameter $\upsilon>0$. Then for every admissible policy $\pi$, every horizon $T\ge1$ and every $x\ge0$,
--
--   $$
--   \mathbb P\big(\|\hat F^\pi_T-F^\pi_T\|>x\big)\le 2KT\exp\Big(-\upsilon\frac{Tx^2}{K^2}\Big).
--   $$
--
--   Here $\hat F^\pi_T$ is the empirical distribution of the rewards the policy collected and $F^\pi_T$ the pseudo empirical distribution $\frac1T\sum_i\tau_i(T)F^{(i)}$. The bound is uniform over policies and drives every horizon-gap estimate of the paper.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - encoding: probabilities and expectations of ‖F̂ − F‖, presupposed to exist → P of an event is the measure M.P (an outer measure on a non-measurable set) and E is the Bochner integral (0 for a non-integrable function), with no measurability hypothesis; reason: on every instance where the source's probabilities and expectations exist they are these values, so no instance of the source changes
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.9, Lemma 2

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Lemma 2 (Empirical Distribution Tail Bound), Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.9:
"Suppose that Requirement 2 of stability holds, then
P(‖F̂^π_T − F^π_T‖ > x) ≤ 2KT exp(−υ T x²/K²), ∀T ≥ 1, x ≥ 0."

Stated for every admissible policy `π` (the paper's `π ∈ Π`). The probability is `M.P` of
the event, compared in `ℝ≥0∞`. -/
theorem lemma_2 {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (M : BanditModel K Ω 𝒱) (υ : ℝ)
    (hReq2 : StabilityReq2 S N M υ) (π : Policy K 𝒱) (T : ℕ) (hT : 1 ≤ T) (x : ℝ)
    (hx : 0 ≤ x) :
    M.P {ω | x < N (empPolicy S M π T ω - pseudoEmp S M π T ω)} ≤
      ENNReal.ofReal (2 * K * T * Real.exp (-(υ * T * x ^ 2 / K ^ 2))) := by sorry

end EDPMBandit
