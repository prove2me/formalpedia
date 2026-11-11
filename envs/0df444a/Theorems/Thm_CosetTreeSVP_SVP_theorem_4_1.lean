-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_theorem_4_1
-- name    : CosetTreeSVP.SVP.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:31:59.807609+00:00
-- url     : https://prove2.me/theorems/ef2b719f-0285-43c5-9df5-49281c9de99b
-- title:
--   Theorem 4.1 — a randomized algorithm solves SVP on every lattice with probability ≥ 2/3 in worst-case time and space 2^{n/2+o(n)}
-- statement:
--   **Theorem 4.1.** There are a program $P$ of the randomized log-cost rational RAM, a function $g$ with $g(n)/n \to 0$ and an exponent $K$ such that for every $n \ge 1$ and every nonsingular basis $B \in \mathbb Q^{n\times n}$ of bit length $\ell$:
--
--   - on every coin tape $P$ halts within bit time and bit space
--   $$2^{n/2+g(n)}\,(\ell+1)^K;$$
--   - with probability at least $2/3$ (a measurable event) it outputs the integer coefficient vector $x$ of a shortest nonzero vector $Bx$ of $L(B)$.
--
--   This is the paper's main result for SVP (Theorem 1.1, item 1): the first $2^{n/2+o(n)}$-time and -space algorithm for exact SVP on every lattice, matching the time exponent of discrete-Gaussian-based methods.
--
--   **Formalization Note.** The statement is `SuperlatSVP.SolvesSVPWithin P K (2^{n/2+g n}) (2^{n/2+g n}) B` (published), with $P$, $g$, $K$ fixed before $n$ and $B$.
--
--   Differences from the source:
--   - encoding: 'a randomized classical algorithm … in worst-case time and space 2^{n/2+o(n)}', input a basis B ∈ ℝ^{n×n}, output a shortest nonzero vector → one program of TwMSOCount.Main on a rational basis, bit time and bit space on every coin tape, output the integer coefficient vector; reason: a machine input is finite; the coefficient vector determines the lattice vector; the paper treats real arithmetic as exact with polynomial precision (p. 11), which is the solver's burden
--   - reading: polynomial factors in the input bit length are omitted (p. 11) → the bounds carry a factor (ℓ+1)^K for the input bit length ℓ; reason: the paper's own convention (p. 11); with ℓ ≤ poly(n), as the paper assumes, it is 2^{o(n)} and the bound is the printed one
--   - encoding: o(n) → one g with g(n)/n → 0, the same for time and space, fixed before n and B; every n ≥ 1; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 14 (PDF 16), Theorem 4.1

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_SuperlatSVP_SolvesSVPWithin

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem theorem_4_1 :
    ∃ (P : Program) (g : ℕ → ℝ) (K : ℕ),
      Tendsto (fun n => g n / n) atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        SuperlatSVP.SolvesSVPWithin P K ((2 : ℝ) ^ ((n : ℝ) / 2 + g n))
          ((2 : ℝ) ^ ((n : ℝ) / 2 + g n)) B := by sorry

end CosetTreeSVP.SVP
