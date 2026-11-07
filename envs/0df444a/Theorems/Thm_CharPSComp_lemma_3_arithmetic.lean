-- Prove2me | Theorems.Thm_CharPSComp_lemma_3_arithmetic
-- name    : CharPSComp.lemma_3_arithmetic
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:49.928496+00:00
-- url     : https://prove2.me/theorems/ccf8a817-3d39-4ccb-9852-86f16ccd4b3b
-- title:
--   Lemma 3 (part 3 of 3: arithmetic in $E$; parts 1–2: lemma_3_construction, lemma_3_units) — $O(d)$ addition, $O(d\log d\log\log d)$ multiplication and reduction
-- statement:
--   This item is the arithmetic clause of Lemma 3; the other clauses are `CharPSComp.lemma_3_construction` and `CharPSComp.lemma_3_units`.
--
--   There are three programs (addition, multiplication, reduction), an absolute constant $C>0$ and a word exponent $\kappa$ such that for every admissible $M$, every nonzero commutative ring $R$, every $d\ge1$ and every monic $H\in R[z]$ of degree $d$, on input words $[d]$ and ring cells holding the $d+1$ coefficients of $H$ followed by the operands' coordinates:
--
--   1. addition of two elements of $E=R[z]/(H)$ (given by $d$ coordinates each) halts at cost at most $Cd$;
--   2. multiplication in $E$ halts at cost at most $C\,d\log d\log\log d$ and working space at most $Cd$;
--   3. reduction modulo $H$ of a polynomial of degree less than $2d$ halts at cost at most $C\,d\log d\log\log d$ and working space at most $Cd$;
--
--   each writing the $d$ coordinates of the result (the representative of degree $<d$) from ring cell $3d+1$, without writing into the input, with every word below $(d+2)^\kappa$.
--
--   These are the coordinate costs that every transform and every matrix product over $E$ is charged.
--
--   **Formalization Note** $\log$ is $\max\{1,\log_2\}$. The constant does not depend on $M$, so the programs cannot rely on the multiplication instruction.
--
--   Differences from the source:
--   - generalization: $R$ of characteristic $p$ and $h\in\mathbb F_p[z]$ monic irreducible of degree $d$, carried into $R[z]$ → every nonzero commutative $R$ and every monic $H\in R[z]$ of degree $d\ge1$; reason: the paper's $E$ is the case $H=$ the image of $h$, which is monic of degree $d$; Cantor–Kaltofen multiplication and Newton division by a monic polynomial work over any commutative ring
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O(\cdot)$ with absolute constants → one triple of programs and constants $C,\kappa$ chosen before $M$, $R$, $d$, $H$; reason: the lemma's $O(d)$ and $O(d\log d\log\log d)$ carry no subscript
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(d+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - encoding: elements of $E$ in coordinates over $R$ → $d$ coefficients of the representative of degree $<d$ in consecutive ring cells; reason: the page's coordinates
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 3, p.8 (PDF p.9), with Appendix B, p.22

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible
import Definitions.Def_CharPSComp_J

open Polynomial

universe u

namespace CharPSComp

/-- Lemma 3 (Transform data and extension arithmetic), part (iii): arithmetic in `E`, Zhu, *Faster
Power Series Composition in Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256
e63e0527…), p.8 (PDF p.9). Companion items: `lemma_3_construction` (part (i)) and `lemma_3_units`
(part (ii)).

"In coordinates over R, addition in E costs O(d) operations. Multiplication in E, or reduction of a
polynomial of degree less than 2d modulo h, takes O(d log d log log d) operations and O(d) space."

There are three programs (addition, multiplication, reduction), an absolute constant `C` and a word
exponent `κ` such that for every admissible `M`, every nonzero commutative ring `R`, every `d ≥ 1`
and every monic `H ∈ R[z]` of degree `d`: on input words `[d]` and ring cells holding the `d + 1`
coefficients of `H` followed by the operands' coordinates, each program halts with the coordinates of
the result (the representative of degree `< d`) from ring cell `3d + 1`, without writing into the
input, with words `< (d + 2)^κ`; addition costs `≤ C d`; multiplication and reduction cost
`≤ C d log d log log d` and use working space `≤ C d`.

**Formalization Note** `log` is the paper's `max{1, log₂}`. Elements of `E = R[z]/(H)` are given by
their `d` coordinates in `1, z̄, …, z̄^{d−1}`; the product is `(A·B) mod H` and the reduction is
`F mod H` (`%ₘ`). The constant does not depend on `M`. -/
theorem lemma_3_arithmetic :
    ∃ (Padd Pmul Pred : Program) (C : ℝ) (κ : ℕ), 0 < C ∧
      ∀ M : ℕ → ℕ, Admissible M → ∀ (R : Type u) [CommRing R] [Nontrivial R],
      ∀ (d : ℕ) (H : R[X]), 1 ≤ d → H.Monic → H.natDegree = d →
      ∀ a b F : ℕ → R,
        (∃ steps : ℕ,
          let s := run M Padd (initState [(d : ℤ)]
            ((List.range (d + 1)).map H.coeff ++ (List.range d).map a ++ (List.range d).map b))
            steps
          s.halted = true ∧
          (∀ i < d, s.rmem (3 * d + 1 + i) = (polyOf a d + polyOf b d).coeff i) ∧
          (s.cost : ℝ) ≤ C * d ∧
          s.maxWord < (d + 2) ^ κ ∧
          s.ReadOnly 1 (3 * d + 1)) ∧
        (∃ steps : ℕ,
          let s := run M Pmul (initState [(d : ℤ)]
            ((List.range (d + 1)).map H.coeff ++ (List.range d).map a ++ (List.range d).map b))
            steps
          s.halted = true ∧
          (∀ i < d, s.rmem (3 * d + 1 + i) = ((polyOf a d * polyOf b d) %ₘ H).coeff i) ∧
          (s.cost : ℝ) ≤ C * d * lg d * lg (lg d) ∧
          (s.space : ℝ) ≤ C * d ∧
          s.maxWord < (d + 2) ^ κ ∧
          s.ReadOnly 1 (3 * d + 1)) ∧
        (∃ steps : ℕ,
          let s := run M Pred (initState [(d : ℤ)]
            ((List.range (d + 1)).map H.coeff ++ (List.range (2 * d)).map F))
            steps
          s.halted = true ∧
          (∀ i < d, s.rmem (3 * d + 1 + i) = (polyOf F (2 * d) %ₘ H).coeff i) ∧
          (s.cost : ℝ) ≤ C * d * lg d * lg (lg d) ∧
          (s.space : ℝ) ≤ C * d ∧
          s.maxWord < (d + 2) ^ κ ∧
          s.ReadOnly 1 (3 * d + 1)) := by sorry

end CharPSComp
