-- Prove2me | Theorems.Thm_ExplicitExpanders_Sizes_log_ratio_irrational
-- name    : ExplicitExpanders.Sizes.log_ratio_irrational
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:12:53.239996+00:00
-- url     : https://prove2.me/theorems/edb699bf-5190-49cb-b4d4-3146a25914fe
-- title:
--   Proof of Lemma 2.2 — $\log q_1/\log q_2$ is irrational for distinct primes
-- statement:
--   Let $q_1$ and $q_2$ be distinct prime numbers. Then the real number
--
--   $$
--   \alpha=\frac{\log q_1}{\log q_2}
--   $$
--
--   is irrational.
--
--   This is the first sentence of the proof of Lemma 2.2. Irrationality of $\alpha$ is what makes the multiples $k\alpha$ spread out modulo $1$, which in turn lets powers $q_1^{k_1}$ come arbitrarily close, multiplicatively, to powers $q_2^{k_2}$.
--
--   **Formalization Note** $\log$ is the natural logarithm `Real.log`; the ratio does not depend on the base. Primes are at least $2$, so $\log q_2>0$ and the quotient is not a division by zero.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 7, proof of Lemma 2.2 (first sentence)

import Mathlib

namespace ExplicitExpanders.Sizes

/-- Proof of Lemma 2.2 (arXiv:2003.11673v1, p. 7), first sentence: for distinct primes `q₁, q₂`
the constant `α = log q₁ / log q₂` is irrational. -/
theorem log_ratio_irrational {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) :
    Irrational (Real.log q₁ / Real.log q₂) := by sorry

end ExplicitExpanders.Sizes
