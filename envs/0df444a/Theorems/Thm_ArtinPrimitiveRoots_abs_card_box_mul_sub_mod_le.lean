-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_abs_card_box_mul_sub_mod_le
-- name    : ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:23:16.686084+00:00
-- url     : https://prove2.me/theorems/edc32d57-b402-48a1-a604-3b4d967f98e7
-- title:
--   Proof of [21] Lemma 3.3, (3.24)–(3.28) — box points on the hyperbola pq ≡ a (mod nS) with fixed residues mod S, with Kloosterman error
-- statement:
--   Let $n \ge 1$, let $S \ge 1$ be squarefree, and let $x_0, y_0, a$ be integers with $a$ coprime to $n$ and $a \equiv x_0y_0 \pmod S$. Take integers $A_1 \le B_1$ and $A_2 \le B_2$.
--
--   Count the $(p, q) \in [A_1, B_1) \times [A_2, B_2)$ with $p \equiv x_0$, $q \equiv y_0 \pmod S$ and $pq \equiv a \pmod{nS}$. This count differs from
--
--   $$(B_1 - A_1)(B_2 - A_2)\sum_{l \mid n,\ (l, S) = 1}\mu(l)\,\frac nl \Big/ (nS)^2$$
--
--   by at most $3S(nS)^{3/4}\bigl(\tau(nS)(1 + \log nS)\bigr)^3\bigl((B_1 - A_1 + B_2 - A_2 + 2)/n + 1\bigr)$.
--
--   The statement uses only Mathlib.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 15–16, (3.24)–(3.28).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 15–16, proof of Lemma 3.3, (3.24)–(3.28)

import Mathlib

namespace ArtinPrimitiveRoots

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

theorem abs_card_box_mul_sub_mod_le (n S : ℕ) (hn : 0 < n) (hS0 : 0 < S) (hS : Squarefree S)
    (x₀ y₀ a : ℤ) (ha : IsCoprime a (n : ℤ)) (hax : (S : ℤ) ∣ a - x₀ * y₀) (A₁ B₁ A₂ B₂ : ℤ)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ ((n * S : ℕ) : ℤ) ∣ p.1 * p.2 - a)) : ℝ) -
      ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ) *
        (((∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ)) : ℤ) : ℝ) /
          ((n : ℝ) * S) ^ 2| ≤
      3 * S * ((n * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
        (((n * S).divisors.card : ℝ) * (1 + Real.log ((n * S : ℕ) : ℝ))) ^ 3 *
        ((((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) + 2) / n + 1) := by
  sorry

end ArtinPrimitiveRoots
