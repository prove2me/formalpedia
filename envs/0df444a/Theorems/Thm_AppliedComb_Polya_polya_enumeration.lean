-- Prove2me | Theorems.Thm_AppliedComb_Polya_polya_enumeration
-- name    : AppliedComb.Polya.polya_enumeration
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:44:39.868757+00:00
-- url     : https://prove2.me/theorems/fdc92c4b-e5ca-436c-810b-4c792662e4d5
-- title:
--   Theorem 15.11 — Pólya's Enumeration Theorem
-- statement:
--   Let $S$ be a set with $|S| = r$ and $\mathcal C$ the set of colorings $f : S \to \{c_1, \ldots, c_m\}$. Let $G$ be a permutation group of $S$, acting on colorings by $\pi^*(f) = f \circ \pi^{-1}$ and so inducing an equivalence relation on $\mathcal C$. Let $P_G(x_1, \ldots, x_r) = \frac{1}{|G|}\sum_{\pi \in G} x_1^{j_1(\pi)} \cdots x_r^{j_r(\pi)}$ be the cycle index of $G$, where $j_k(\pi)$ is the number of cycles of length $k$ of $\pi$ (fixed points counted as cycles of length $1$). Then
--
--   $$P_G\Bigl(\sum_{i=1}^m c_i,\ \sum_{i=1}^m c_i^2,\ \ldots,\ \sum_{i=1}^m c_i^r\Bigr)$$
--
--   is the generating function for the number of nonequivalent colorings of $S$ in $\mathcal C$: in commuting variables $c_1, \ldots, c_m$, the coefficient of $c_1^{a_1}\cdots c_m^{a_m}$ is the number of equivalence classes of colorings that use each color $c_i$ exactly $a_i$ times. Equivalently,
--
--   $$P_G\Bigl(\sum_i c_i, \ldots, \sum_i c_i^r\Bigr) = \sum_{\langle f\rangle \in \mathcal C/\sim} \ \prod_{s \in S} f(s).$$
--
--   Setting every $c_i = 1$ recovers the number of nonequivalent colorings, $P_G(m, \ldots, m)$.
--
--   **Formalization Note.** $P_G$ is `AppliedComb.Polya.cycleIndex G` in `MvPolynomial (Fin r) ℚ` with $r$ = `Fintype.card S`, and the substitution $x_k \mapsto \sum_i c_i^k$ is `MvPolynomial.bind₁` sending the variable with index `k : Fin r` to $\sum_{i} c_i^{k+1}$. The right side is `AppliedComb.Polya.patternInventory G m` in `MvPolynomial (Fin m) ℚ`, the sum over the classes of `colorSetoid G m` of the weight of a representative. The cycle index is defined from cycle structure alone, so the theorem is not a restatement of its definition.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 302, Theorem 15.11

import Mathlib
import Definitions.Def_AppliedComb_Polya_cycleIndex
import Definitions.Def_AppliedComb_Polya_patternInventory

namespace AppliedComb.Polya

open MvPolynomial

/-- Keller–Trotter, Theorem 15.11 (Pólya's Enumeration Theorem), p. 302. Let `S` be a set with
`|S| = r` and `𝒞` the set of colorings of `S` using the colors `c_1, …, c_m`. If a permutation
group `G` acts on `S` to induce an equivalence relation on `𝒞`, then
`P_G(∑ c_i, ∑ c_i^2, …, ∑ c_i^r)` is the generating function for the number of nonequivalent
colorings of `S` in `𝒞`: substituting the power sum `∑_{i=1}^m c_i^k` for `x_k` (`1 ≤ k ≤ r`)
in the cycle index `P_G` gives the pattern inventory. The variable `X k` (`k : Fin r`) of `P_G`
stands for `x_{k+1}`, and the variable `X i` (`i : Fin m`) for the color `c_{i+1}`. -/
theorem polya_enumeration {S : Type*} [Fintype S] [DecidableEq S]
    (G : Subgroup (Equiv.Perm S)) (m : ℕ) :
    bind₁ (fun k : Fin (Fintype.card S) => ∑ i : Fin m, (X i : MvPolynomial (Fin m) ℚ) ^ (k.val + 1))
        (cycleIndex G) = patternInventory G m := by sorry

end AppliedComb.Polya
