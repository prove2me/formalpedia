-- Prove2me | Theorems.Thm_BorderD4_theorem_6_1
-- name    : BorderD4.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:11.493392+00:00
-- url     : https://prove2.me/theorems/ead1cd81-9ae6-4142-8460-839e305cce6c
-- title:
--   Theorem 6.1: every border $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit for $P_{k+1,n}$ has size $2^{\Omega(n/(k(4\delta)^k))}$
-- statement:
--   Let $F$ be a field of characteristic $0$, and let $P_{k+1,n}$ be the sum of $k+1$ disjoint monomials of degree $n$.
--
--   1. (Theorem 6.1) If a $\overline{\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}}$ circuit of size $s$ computes $P_{k+1,n}$, then
--   $$n\le O\bigl(k(4\delta)^k\log s\bigr)+(2\delta)^{O(k^2)}.$$
--   2. (Theorem 1.4) There is an absolute constant $c\ge 1$ such that, for all $k,\delta\ge 1$ and all $n\ge(2\delta)^{ck^2}$, every such circuit has size at least $2^{\Omega(n/(k(4\delta)^k))}$.
--   3. (Theorem 6.1's last sentence, Corollary 1.5) For all fixed $k$ and $\delta$, every such circuit has size $2^{\Omega(n)}$.
--   4. (Corollary 1.5, with p.4) $P_{k+1,n}$ has an exact $\Sigma^{[k+1]}\Pi\Sigma$ circuit of size $O(kn)$, in which no product gate takes a factor with multiplicity above $1$.
--
--   Together these give an exponential top fan-in hierarchy for border depth-4 circuits of bounded bottom fan-in. The number of factors of a product gate, their multiplicities and the orders of the poles in $\varepsilon$ are unrestricted.
--
--   **Formalization Note** Constants are absolute and chosen before $F,k,\delta,n,s$, except in clause 3, where they depend only on $k,\delta$. $\Sigma^{[k+1]}\Pi\Sigma$ is the model at $\delta=1$ (p.4).
--
--   Differences from the source:
--   - generalization: the size of a circuit, gates plus wires with multi-wires (p.32) → `size` counts a power wire once and counts no input nodes; reason: it is at most the page's size, so the lower bounds for it imply the lower bounds for the page's size; the proof uses only that the distinct bottom polynomials number at most the size; in the upper bound (clause 4) every power wire has multiplicity at most 1, so there `size` is the page's count up to the at most N input nodes
--   - generalization: Theorem 6.1 in §6, with $F$ algebraically closed (p.49) → every field of characteristic $0$; reason: Theorem 1.4 and Corollary 1.5 say so, and the extension of p.26 is the transfer
--   - reading: the constants of $2^{\Omega(n)}$ for fixed $k,\delta$, with $F$ fixed in Corollary 1.5 → constants depending on $k,\delta$ only, chosen before $F$; reason: clause 1 has absolute constants, so this is the strong reading the page's proof gives
--   - encoding: $\log$ and $O(\cdot)$ → `Real.log`, with explicit existential constants; reason: a change of base only changes $A$
--   - encoding: the variables $x_1,\dots,x_N$ → $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$; reason: this is $P_{k+1,n}$ up to renaming
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.1, p.49; Theorem 1.4 and Corollary 1.5, p.6; upper bound O(kn), p.4

import Mathlib
import Definitions.Def_BorderD4_sumProduct
import Definitions.Def_BorderD4_SPSP
import Definitions.Def_BorderD4_BorderComputes
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries
universe u

namespace BorderD4

/-- Theorem 6.1 with Theorem 1.4 and Corollary 1.5: the exponential top fan-in hierarchy for border depth-4 circuits.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 6.1, p.49; Theorem 1.4 and Corollary 1.5, p.6; the upper bound `O(kn)`, p.4.

For a field `F` of characteristic `0`:
1. (Theorem 6.1) if a `Σ^[k]ΠΣΠ^[δ]` circuit of size at most `s` border computes `P_{k+1,n}`, then
   `n ≤ O(k (4δ)^k log s) + (2δ)^{O(k²)}`;
2. (Theorem 1.4) there is an absolute `c ≥ 1` such that for all `k, δ ≥ 1` and all `n ≥ (2δ)^{ck²}`, every such circuit has
   size at least `2^{Ω(n/(k (4δ)^k))}`;
3. (Theorem 6.1's last sentence, Corollary 1.5's second half) for all fixed `k, δ`, every such circuit has size `2^{Ω(n)}`;
4. (Corollary 1.5's first half, p.4) `P_{k+1,n}` has an exact `Σ^[k+1]ΠΣ` circuit of size `O(kn)`.

**Formalization Note** Every constant is absolute and chosen before `F`, `k`, `δ`, `n`, except in clause 3, where the
constants depend only on `k`, `δ`. `log` is the natural logarithm, which only changes `A`. `Σ^[k+1]ΠΣ` is the model
at `δ = 1` (p.4). In clause 4 every wire into a product gate has multiplicity at most `1`, so the circuit's `size`
differs from the page's count of gates plus wires only by the at most `N = (k+1)n` input nodes, and the upper bound
holds for the page's size too. -/
theorem theorem_6_1 :
    (∃ (A : ℝ) (B : ℕ), 0 < A ∧ ∀ (F : Type u) [Field F] [CharZero F] (k δ n s : ℕ),
      1 ≤ k → 1 ≤ δ → 1 ≤ n → 1 ≤ s →
      ∀ C : SPSP (LaurentSeries F) (Fin (k + 1) × Fin n) k δ, BorderComputes C (sumProduct F k n) →
        C.size ≤ s →
        (n : ℝ) ≤ A * k * (4 * δ) ^ k * Real.log s + (2 * δ) ^ (B * k ^ 2)) ∧
    (∃ (c : ℕ) (c' : ℝ), 1 ≤ c ∧ 0 < c' ∧ ∀ (F : Type u) [Field F] [CharZero F] (k δ n : ℕ),
      1 ≤ k → 1 ≤ δ → (2 * δ) ^ (c * k ^ 2) ≤ n →
      ∀ C : SPSP (LaurentSeries F) (Fin (k + 1) × Fin n) k δ, BorderComputes C (sumProduct F k n) →
        (2 : ℝ) ^ (c' * n / (k * (4 * δ) ^ k)) ≤ C.size) ∧
    (∀ k δ : ℕ, 1 ≤ k → 1 ≤ δ → ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧
      ∀ (F : Type u) [Field F] [CharZero F] (n : ℕ), n₀ ≤ n →
      ∀ C : SPSP (LaurentSeries F) (Fin (k + 1) × Fin n) k δ, BorderComputes C (sumProduct F k n) →
        (2 : ℝ) ^ (c * n) ≤ C.size) ∧
    (∃ C₀ : ℕ, ∀ (F : Type u) [Field F] [CharZero F] (k n : ℕ), 1 ≤ k → 1 ≤ n →
      ∃ C : SPSP F (Fin (k + 1) × Fin n) (k + 1) 1, C.eval = sumProduct F k n ∧
        (∀ i m, C.exp i m ≤ 1) ∧ C.size ≤ C₀ * k * n) := by sorry

end BorderD4
