-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_initial_lower
-- name    : ArtinPrimitiveRoots.initial_lower
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T11:19:56.448989+00:00
-- url     : https://prove2.me/theorems/1c5b3c5d-e37f-4d0d-b6dc-5b7cdebb8bb9
-- title:
--   Proof of Proposition 2.1 (OpenAI), (12.22) — the initial lower bound for the mass without small prime factors
-- statement:
--   There are constants $C_s > 0$ and $b_1 > 0$ with the following property. Let $M, c, u$ satisfy (12.1): $M > 0$, $8 \mid M$, $c \in \{2, 4\}$, $(u, M) = 1$, $c \mid u - 1$ and $\bigl(\frac{u-1}{c}, \frac Mc\bigr) = 1$. Let $\Psi$ be $C^\infty$ with closed support in $(1, 2)$, $0 \le \Psi \le 1$ and $\int\Psi > 0$. Let $0 < b < b_1$, $K \ge 1$ and $0.1 < a_1 < \cdots < a_K < 0.2$. Write $w = $ `constructionWeight M c u Ψ x a`, $X_0 = $ `totalMass M c u Ψ x a`, $\mathfrak S_M = $ `singularSeries M`, $L = \log x$ and $\gamma_E$ for Euler's constant. Then for every $\eta > 0$ there is $x_0$ such that for every $x \ge x_0$,
--
--   $$\sum_{P^-(d) > x^b} w(d) \;\ge\; \frac{\mathfrak S_M X_0}{L}\Bigl(\frac{e^{-\gamma_E}}{b}\bigl(1 - C_s e^{-(1/20)/b}\bigr) - \eta\Bigr).$$
--
--   Here $P^-(d) > y$ is `IsRough y d`: $d \ge 1$ and every prime factor of $d$ exceeds $y$. The sum is a `tsum` over all natural numbers $d$.
--
--   **Formalization note.** The $o(1)$ of (12.22) is written as $-\eta$ for $x \ge x_0(\eta)$. The constant $c_s$ is fixed at $1/20$, as the paper says the bound on $e^{-H}$ permits. "Sufficiently small fixed $b$" is $b < b_1$. $C_s$ and $b_1$ are chosen before $M$, $c$, $u$, $\Psi$, $K$ and the marks, matching the paper's "$C_s, c_s > 0$ are absolute". Of the standing assumptions (12.11), only $b$ occurs in the statement.
--
--   OpenAI, *Primitive roots for every admissible integer base* (2026), p. 79: “For sufficiently small fixed $b$, this is large enough for the lower bound in Lemma 11.1; […] Summing the sieve bound with the marks, using (12.20)–(12.21) and the negligible tail in Lemma 12.2, gives $S_b := \sum_{P^-(d)>x^b} w(d) \ge \frac{\mathfrak S_M X_0}{L}\Bigl\{\frac{e^{-\gamma_E}}{b}(1 - C_s e^{-c_s/b}) + o(1)\Bigr\}$, (12.22) where $C_s, c_s > 0$ are absolute; the displayed bound on $e^{-H}$ permits $c_s = 1/20$, after enlarging $C_s$.”
-- source:
--   OpenAI, Primitive roots for every admissible integer base, OpenAI Math Release preprint, October 4, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf (Apache-2.0), p. 79, proof of Proposition 2.1, (12.22)

import Mathlib
import Definitions.Def_ArtinSieve

namespace ArtinPrimitiveRoots

open Real

open Classical in
theorem initial_lower :
    ∃ C_s b₁ : ℝ, 0 < C_s ∧ 0 < b₁ ∧
    ∀ (M c : ℕ) (u : ℤ), 0 < M → 8 ∣ M → (c = 2 ∨ c = 4) → IsCoprime u M →
      (c : ℤ) ∣ u - 1 → IsCoprime ((u - 1) / c) ((M : ℤ) / c) →
    ∀ Ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) Ψ → tsupport Ψ ⊆ Set.Ioo 1 2 →
      (∀ y, 0 ≤ Ψ y) → (∀ y, Ψ y ≤ 1) → 0 < ∫ y, Ψ y →
    ∀ b : ℝ, 0 < b → b < b₁ →
    ∀ K : ℕ, 1 ≤ K → ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      singularSeries M * totalMass M c u Ψ x a / log x *
          (exp (-eulerMascheroniConstant) / b * (1 - C_s * exp (-(1 / 20) / b)) - η) ≤
        ∑' d : ℕ, (if IsRough (x ^ b) d then constructionWeight M c u Ψ x a d else 0) := by
  sorry

end ArtinPrimitiveRoots
