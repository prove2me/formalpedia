-- Prove2me | Theorems.Thm_FernauIntersection_Bounded_theorem_9_1
-- name    : FernauIntersection.Bounded.theorem_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:33:17.837201+00:00
-- url     : https://prove2.me/theorems/f22ed108-7d0c-4b18-8fad-c354eac3b8ff
-- title:
--   Theorem 9.1 — generalized Chinese remainder theorem
-- statement:
--   Let $k\in\mathbb N$, let $m_1,\dots,m_k$ be positive integers (moduli) and $r_1,\dots,r_k$ integers (residues), and consider the system of congruences
--   $$x\equiv r_i\pmod{m_i}\qquad(i=1,\dots,k).$$
--
--   **Theorem 9.1 (Generalized Chinese Remainder Theorem).**
--   1. The system has an integral solution $x$ if and only if $\gcd(m_i,m_j)$ divides $r_i-r_j$ for all pairs $i\ne j$.
--   2. All integral solutions are congruent modulo $\operatorname{lcm}(m_1,\dots,m_k)$.
--   3. There is a natural number $x$ with $x\equiv r_i\pmod{m_i}$ for all $i$ if and only if $r_i\equiv r_j\pmod{\gcd(m_i,m_j)}$ for all $i,j$.
--
--   Unlike the classical Chinese remainder theorem, the moduli need not be pairwise coprime. In the paper the theorem decides which pairs of vertices of different automata are joined by the edges $E_5$ of the Multicolored Clique instance built in the proof of Theorem 9.2.
--
--   **Formalization Note.** The moduli are natural numbers with $m_i>0$, the residues integers, and the congruences are Mathlib's `Int.ModEq`. The lcm of the empty family ($k=0$) is $1$.
--
--   Differences from the source:
--   - encoding: moduli m_i and residues r_i, indices 1..k → moduli m : Fin k → ℕ with m i > 0, residues r : Fin k → ℤ, 0-based indices; reason: the source's moduli are positive integers; no instance changes
-- source:
--   Fernau, Hoffmann, Wehar (2021), arXiv:2108.05244v1, Theorem 9.1, p. 23:18 (PDF p. 18)

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Fintype.Fin

namespace FernauIntersection.Bounded

/-- Theorem 9.1 (Generalized Chinese Remainder Theorem, p. 23:18), for `k` congruences
`x ≡ rᵢ (mod mᵢ)` with positive moduli `mᵢ` and integer residues `rᵢ`: (1) an integral solution
exists iff `gcd(mᵢ, mⱼ) ∣ rᵢ - rⱼ` for all `i ≠ j`; (2) all integral solutions are congruent modulo
`lcm(m₁, …, m_k)`; (3) a natural-number solution exists iff `rᵢ ≡ rⱼ (mod gcd(mᵢ, mⱼ))` for all
`i, j`. -/
theorem theorem_9_1 (k : ℕ) (m : Fin k → ℕ) (hm : ∀ i, 0 < m i) (r : Fin k → ℤ) :
    ((∃ x : ℤ, ∀ i, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        ∀ i j, i ≠ j → ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ r i - r j) ∧
      (∀ x y : ℤ, (∀ i, x ≡ r i [ZMOD (m i : ℤ)]) → (∀ i, y ≡ r i [ZMOD (m i : ℤ)]) →
        x ≡ y [ZMOD ((Finset.univ.lcm m : ℕ) : ℤ)]) ∧
      ((∃ x : ℕ, ∀ i, (x : ℤ) ≡ r i [ZMOD (m i : ℤ)]) ↔
        ∀ i j, r i ≡ r j [ZMOD ((Nat.gcd (m i) (m j) : ℕ) : ℤ)]) := by sorry

end FernauIntersection.Bounded
