-- Prove2me | Theorems.Thm_Dvir_kakeya_lower_bound
-- name    : Dvir.kakeya_lower_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T12:41:14.906523+00:00
-- url     : https://prove2.me/theorems/40c46136-5666-444a-96ff-3b716ec1e126
-- title:
--   Dvir's finite-field Kakeya bound $|K|\ge\binom{q+n-1}{n}$
-- statement:
--   A **Kakeya set** in $F^n$, where $F$ is a finite field of cardinality $q$, is a set containing a line in every direction: for every nonzero $b \in F^n$ there is $a \in F^n$ with $\{a + t b : t \in F\} \subseteq K$.
--
--   **Dvir's theorem** (2008): every Kakeya set $K \subseteq F^n$ satisfies
--
--   $$
--   |K| \;\ge\; \binom{q + n - 1}{n}.
--   $$
--
--   Since $\binom{q+n-1}{n} \approx q^n/n!$, this says Kakeya sets occupy a positive proportion of $F^n$, answering (in the strongest way) a question posed by Wolff in 1996 as the finite-field analogue of the classical Kakeya problem in $\mathbb{R}^n$. Dvir's two-page proof launched the polynomial method in combinatorics: before 2008, the best finite-field bounds were of the form $|K| \ge c_n q^{n-\epsilon}$ from sum-product arguments, and no positive-proportion bound was known.
--
--   The bound above is the basic (degree $q-1$) form of the argument; Dvir's follow-up with the multiplicity trick gives the sharp $|K| \ge c_n q^n$ with explicit $c_n \to e^{-n}$, but even the basic form implies $|K|/q^n \ge 1/n!$.
--
--   **Formalization Note** The line through $a$ in direction $b$ is parametrized as `(fun j => a j + t * b j)`; decidability and `Fintype ↥K` instances are classical. Not in Mathlib as of this Mathlib revision (the analytic sticky-Kakeya program on this platform is unrelated).
-- source:
--   Z. Dvir, On the size of Kakeya sets in finite fields, J. Amer. Math. Soc. 22 (2009), 593–597 (arXiv:0803.2336), Theorem 1. Basic (degree q−1) form of the polynomial-method argument.

import Mathlib

namespace Dvir

open Classical in
theorem kakeya_lower_bound {F : Type*} [Field F] [Fintype F] {n : ℕ} (hn : 1 ≤ n)
    (K : Set (Fin n → F)) [DecidablePred (· ∈ K)] [Fintype ↥K]
    (hK : ∀ b : Fin n → F, b ≠ 0 → ∃ a : Fin n → F, ∀ t : F, (fun j => a j + t * b j) ∈ K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ Fintype.card ↥K := by
  sorry

end Dvir
