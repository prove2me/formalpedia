-- Prove2me | Theorems.Thm_EDPMBandit_expected_empirical_eq_pseudo
-- name    : EDPMBandit.expected_empirical_eq_pseudo
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:20.546378+00:00
-- url     : https://prove2.me/theorems/7320434e-83ea-4392-87f9-f656d400d08b
-- title:
--   Proof of Theorem 3, first display — $\mathbb E\hat F^\pi_T=\mathbb EF^\pi_T$
-- statement:
--   For every admissible policy $\pi$, every horizon $T\ge1$ and every $x\in\mathbb R$,
--
--   $$
--   \mathbb E\big[\hat F^\pi_T(x)\big]=\mathbb E\big[F^\pi_T(x)\big].
--   $$
--
--   The empirical distribution of the collected rewards is an unbiased estimate of the pseudo empirical distribution: the arm chosen in round $t$ depends only on the past, and the reward it then yields is a fresh draw from that arm's law.
--
--   **Formalization Note** Arms are `Fin K`; the reward stack $X$ is indexed from $0$ (the paper's $X_{i,k+1}$ is `X i k`); distribution functions are functions $\mathbb R\to\mathbb R$ in a submodule $L$ of $\mathbb R^{\mathbb R}$ with a seminorm $\|\cdot\|$; probabilities are values of the measure $P$ in $[0,\infty]$ and expectations are Bochner integrals; $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: distribution functions on the extended real line, in a seminormed space L containing all distributions → functions ℝ → ℝ; L any submodule of ℝ → ℝ containing every indicator 𝕀_{[a,∞)} and every distribution function, with a seminorm on L; reason: the values at ±∞ are 0 and 1 for every distribution; indicators are distribution functions of point masses, so the same spaces are allowed
--   - encoding: arms {1,…,K}, rewards X_{i,t} (t ≥ 1), admissible policies (1)–(3) with π_t H_{t−1}-measurable, natural log → arms Fin K, rewards X i k with zero-based sample index, policies as jointly measurable decision rules of V and the observed history; Real.log; reason: a choice is H_{t−1}-measurable iff it is a measurable function of (V, history) (Doob–Dynkin); same policy class
--   - encoding: E F̂^π_T = E F^π_T (expectation of a distribution-valued random variable) → equality of the expectations of F̂^π_T(x) and F^π_T(x) for every x ∈ ℝ; reason: the displays on p.25 compute the expectation pointwise (E[𝕀_{[X,∞]} | π_t] = F^{(π_t)})
--   - encoding: horizon T, a number of rounds (F̂^π_T and F^π_T divide by T) → T : ℕ with the hypothesis 1 ≤ T; reason: excludes only T = 0, where F̂^π_T and F^π_T are undefined
-- source:
--   Cassel–Mannor–Zeevi, A General Framework for Bandit Problems Beyond Cumulative Objectives, arXiv:1806.01380v3, p.25, proof of Theorem 3, first display

import Mathlib
import Definitions.Def_EDPMBandit_Model
import Definitions.Def_EDPMBandit_Conditions

open MeasureTheory ProbabilityTheory

namespace EDPMBandit

/-- Proof of Theorem 3, first display, Cassel–Mannor–Zeevi, arXiv:1806.01380v3, p.25: "First,
notice that E F̂^π_T = E F^π_T for any π ∈ Π."

**Formalization Note.** The expectation of a distribution-function-valued random variable is
taken pointwise: for every `x ∈ ℝ`, `E[F̂^π_T(x)] = E[F^π_T(x)]`. Stated for every admissible
policy and every horizon `T ≥ 1`. -/
theorem expected_empirical_eq_pseudo {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {𝒱 : Type*}
    [MeasurableSpace 𝒱] (S : DistSpace) (M : BanditModel K Ω 𝒱) (π : Policy K 𝒱) (T : ℕ)
    (hT : 1 ≤ T) (x : ℝ) :
    ∫ ω, (empPolicy S M π T ω : ℝ → ℝ) x ∂M.P = ∫ ω, (pseudoEmp S M π T ω : ℝ → ℝ) x ∂M.P := by sorry

end EDPMBandit
