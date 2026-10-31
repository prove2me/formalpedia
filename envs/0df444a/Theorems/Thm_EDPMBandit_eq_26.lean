-- Prove2me | Theorems.Thm_EDPMBandit_eq_26
-- name    : EDPMBandit.eq_26
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:58.403221+00:00
-- url     : https://prove2.me/theorems/18724ac4-0fd6-407a-b4d7-d4ac32df513b
-- title:
--   Eq. (26) — concentration of $U(\hat F^{(i)}_t)$: $\mathbb P(|U(\hat F^{(i)}_t)-U(F^{(i)})|\ge x)\le4e^{-t\varphi(x)}$
-- statement:
--   Let $U$ be stable with parameters $\upsilon,b>0$, $q\ge1$, and let $\varphi$ be as in (15). Then for every arm $i$, every $t\ge1$ and every $x>0$,
--
--   $$
--   \mathbb P\big(|U(\hat F^{(i)}_t)-U(F^{(i)})|\ge x\big)\le4\exp\big(-t\varphi(x)\big).
--   $$
--
--   This concentration inequality for the U-UCB index is the input of the UCB argument in the proof of Theorem 2.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - encoding: (26) written for the sample size t and the level x of Requirement 2 → hypotheses 1 ≤ t and 0 < x; reason: these are the ranges of Requirement 2, which (26) applies (F̂^(i)_0 is undefined, and (26) is used at x = φ⁻¹(γ log t/s) > 0)
--   - encoding: probabilities and expectations of ‖F̂ − F‖, presupposed to exist → P of an event is the measure M.P (an outer measure on a non-measurable set) and E is the Bochner integral (0 for a non-integrable function), with no measurability hypothesis; reason: on every instance where the source's probabilities and expectations exist they are these values, so no instance of the source changes
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.23, eq. (26)

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions
import Definitions.Def_EDPMBandit_UUCB

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Eq. (26), proof of Theorem 2, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.23: for a stable
EDPM, every arm `i`, every `t ≥ 1` and `x > 0`,
`P(|U(F̂^{(i)}_t) − U(F^{(i)})| ≥ x) ≤ 4 exp(−t φ(x))`, with `φ` of p.8. -/
theorem eq_26 {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (U : S.L → ℝ) (M : BanditModel K Ω 𝒱) (υ b q : ℝ)
    (hstab : IsStable S N U M υ b q) (i : Fin K) (t : ℕ) (ht : 1 ≤ t) (x : ℝ) (hx : 0 < x) :
    M.P {ω | x ≤ |U (empArm S M i t ω) - U (armDist S M i)|} ≤
      ENNReal.ofReal (4 * Real.exp (-(t * phi υ b q x))) := by sorry

end EDPMBandit
