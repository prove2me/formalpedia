-- Prove2me | Theorems.Thm_EDPMBandit_lemma_6
-- name    : EDPMBandit.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:01:59.654992+00:00
-- url     : https://prove2.me/theorems/d9719124-cbd1-46c2-af8b-8504953cb73d
-- title:
--   Lemma 6 — moment bounds for $\|\hat F^\pi_T-F^\pi_T\|$
-- statement:
--   Assume Requirement 2 of stability with parameter $\upsilon>0$. Let $d\ge1$ be an integer, $\pi$ an admissible policy and $K,T$ such that $\log(KT)\ge3$. Write $Z=\|\hat F^\pi_T-F^\pi_T\|$ and $m=\lceil d/2-1\rceil$. Then:
--
--   1. $\displaystyle \mathbb E Z^d\le[1+d\,m!]\Big(\frac{K^2\log KT}{\upsilon T}\Big)^{d/2}$;
--   2. if $T\ge 4dK^2\log(KT)/\upsilon$, then $\displaystyle\mathbb E Z^d\le2\Big(\frac{K^2\log KT}{\upsilon T}\Big)^{1/2}$;
--   3. if $T\ge 4dK^2\log(KT)/\upsilon$ and $M\ge0$ satisfies $M^2\ge 4dK^2\log(KT)/(\upsilon T)$, then $\displaystyle\mathbb E\big[Z^d\,\mathbb 1\{Z>M\}\big]\le\frac1{T^2}$.
--
--   These moment bounds control the horizon gaps $\mathbb E[U(\hat F^\pi_T)-U(F^\pi_T)]$.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm. The power $d/2$ is `Real.rpow`.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - reading: M² ≥ 4dK² log KT/(υT) for a threshold M → 0 ≤ M and M² ≥ 4dK² log KT/(υT); reason: M is a threshold that the proof compares with x₁ = (4dK² log KT/(υT))^{1/2} ≥ 0 (x₁ ≤ M); for M < 0 the indicator is 1 and the claim would bound the full moment by 1/T², which is not meant
--   - encoding: m = ⌈d/2 − 1⌉; "for all T ≥ …" → m = (d − 1)/2 in ℕ; the conditions on T as hypotheses on the fixed T; reason: ⌈d/2 − 1⌉ = (d − 1)/2 (floor) for every d ≥ 1; K and T are fixed in the statement
--   - encoding: probabilities and expectations of ‖F̂ − F‖, presupposed to exist → P of an event is the measure M.P (an outer measure on a non-measurable set) and E is the Bochner integral (0 for a non-integrable function), with no measurability hypothesis; reason: on every instance where the source's probabilities and expectations exist they are these values, so no instance of the source changes
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.25, Lemma 6

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Lemma 6, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.25: "Suppose that Requirement 2 of
stability holds. Then for any integer d ≥ 1, policy π ∈ Π, and K, T such that log KT ≥ 3, we have
that:
1. E‖F̂^π_T − F^π_T‖^d ≤ [1 + d m!] (K² log KT/(υT))^{d/2}, where m = ⌈d/2 − 1⌉;
2. E‖F̂^π_T − F^π_T‖^d ≤ 2 (K² log KT/(υT))^{1/2} for all T ≥ 4dK² log KT/υ;
3. E[‖F̂^π_T − F^π_T‖^d 𝟙{‖F̂^π_T − F^π_T‖ > M}] ≤ 1/T² for all T ≥ 4dK² log KT/υ,
   M² ≥ 4dK² log KT/(υT)."

**Formalization Note.** `m = ⌈d/2 − 1⌉` is the natural-number quotient `(d - 1) / 2` (equal for
every `d ≥ 1`: d = 1, 2 give 0; d = 3, 4 give 1; …). `log KT = Real.log (K * T)`, natural
logarithm. The power `d/2` is `Real.rpow`. "For all T ≥ …" is a hypothesis on the fixed `T`
of the statement. The threshold `M` (called `Mth`) is nonnegative, as in the proof, which
compares it with `x₁ ≥ 0`. Expectations are Bochner integrals over `M.P`. -/
theorem lemma_6 {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*} [MeasurableSpace 𝒱]
    (S : DistSpace) (N : Seminorm ℝ S.L) (M : BanditModel K Ω 𝒱) (υ : ℝ)
    (hReq2 : StabilityReq2 S N M υ) (d : ℕ) (hd : 1 ≤ d) (π : Policy K 𝒱) (T : ℕ)
    (hKT : 3 ≤ Real.log ((K : ℝ) * T)) :
    (∫ ω, N (empPolicy S M π T ω - pseudoEmp S M π T ω) ^ d ∂M.P) ≤
        (1 + (d : ℝ) * (((d - 1) / 2).factorial : ℝ)) *
          ((K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / (υ * T)) ^ ((d : ℝ) / 2) ∧
      (4 * (d : ℝ) * (K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / υ ≤ T →
        (∫ ω, N (empPolicy S M π T ω - pseudoEmp S M π T ω) ^ d ∂M.P) ≤
          2 * ((K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / (υ * T)) ^ (1 / 2 : ℝ)) ∧
      (∀ Mth : ℝ, 0 ≤ Mth →
        4 * (d : ℝ) * (K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / υ ≤ T →
        4 * (d : ℝ) * (K : ℝ) ^ 2 * Real.log ((K : ℝ) * T) / (υ * T) ≤ Mth ^ 2 →
        (∫ ω, (if Mth < N (empPolicy S M π T ω - pseudoEmp S M π T ω) then
            N (empPolicy S M π T ω - pseudoEmp S M π T ω) ^ d else 0) ∂M.P) ≤
          1 / (T : ℝ) ^ 2) := by sorry

end EDPMBandit
