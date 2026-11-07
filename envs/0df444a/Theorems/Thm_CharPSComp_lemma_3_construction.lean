-- Prove2me | Theorems.Thm_CharPSComp_lemma_3_construction
-- name    : CharPSComp.lemma_3_construction
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:11:03.948699+00:00
-- url     : https://prove2.me/theorems/5963ae97-d2db-46a1-b744-a0ab45f65e44
-- title:
--   Lemma 3 (part 1 of 3: construction; parts 2–3: lemma_3_units, lemma_3_arithmetic) — transform data in $O_p(N\log N)$
-- statement:
--   This item is the construction clause of Lemma 3; the unit clause is `CharPSComp.lemma_3_units` and the arithmetic clause is `CharPSComp.lemma_3_arithmetic`.
--
--   Fix a prime $p$. There are one program, a constant $C>0$ and a word exponent $\kappa$ such that for every admissible $M$, every nonzero commutative ring $R$ of characteristic $p$ and every power $N=p^j$: the run started with $W[0]=N$ halts at cost at most $C\,N\log N$, working space at most $CN$, every word below $(N+2)^\kappa$, without overwriting $W[0]$, and its word cells $1,2,\dots$ then hold the table $\mathcal T$ of some admissible transform data $(h,\rho)$: $h\in\mathbb F_p[z]$ monic irreducible of degree $d$ and $\rho\in\mathbb F_p[z]/(h)$ of order at least $L_{\max}$.
--
--   The table supplies the evaluation points $\rho^i$ and the constants of the chirp-$z$ transforms of Lemma 4.
--
--   **Formalization Note** $\log$ is $\max\{1,\log_2\}$. The table layout is `tableWords`; "the data for reduction modulo $h$" is $h$ itself (see the definition).
--
--   Differences from the source:
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{p}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $p$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $p$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(N+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - reading: the table $\mathcal T$ contains "the data for reduction modulo $h$" → $\mathcal T$ contains $h$ itself as that data; reason: the page does not fix the data; any reciprocal for fast division is recomputable from $h$ within the cost of one reduction (Appendix B)
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 3, p.8 (PDF p.9), with §3.3.1 and Appendix B

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible
import Definitions.Def_CharPSComp_tableWords

open Polynomial

universe u

namespace CharPSComp

/-- Lemma 3 (Transform data and extension arithmetic), part (i): the construction, Zhu, *Faster
Power Series Composition in Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256
e63e0527…), p.8 (PDF p.9). Companion items: `lemma_3_units` (part (ii)) and `lemma_3_arithmetic`
(part (iii)).

"BuildTransformData(N, p) deterministically constructs such an h, a ratio ρ of order at least
L_max and their table T in O_p(N log N) operations and O_p(N) space."

For each prime `p` there are one program, a constant `C` and a word exponent `κ` such that for every
admissible `M`, every nonzero commutative ring `R` of characteristic `p` and every power `N = pʲ`,
the run started with `W[0] = N` halts at cost `≤ C N log N`, working space `≤ C N`, words
`< (N + 2)^κ`, without overwriting `W[0]`, and its word cells `1, 2, …` then hold the table `T` of
some monic irreducible `h ∈ F_p[z]` of degree `d` and some `ρ ∈ F_p[z]/(h)` of order `≥ L_max`.

**Formalization Note** `log` is the paper's `max{1, log₂}`. The table layout is `tableWords`
(`Def_CharPSComp_tableWords`), whose "data for reduction modulo h" is `h` itself. -/
theorem lemma_3_construction (p : ℕ) [Fact p.Prime] :
    ∃ (P : Program) (C : ℝ) (κ : ℕ), 0 < C ∧
      ∀ M : ℕ → ℕ, Admissible M → ∀ (R : Type u) [CommRing R] [Nontrivial R] [CharP R p],
      ∀ j : ℕ,
        ∃ steps : ℕ,
          let s := run M P (initState [((p ^ j : ℕ) : ℤ)] ([] : List R)) steps
          s.halted = true ∧
          (s.cost : ℝ) ≤ C * (p ^ j : ℕ) * lg (p ^ j : ℕ) ∧
          (s.space : ℝ) ≤ C * (p ^ j : ℕ) ∧
          s.maxWord < (p ^ j + 2) ^ κ ∧
          s.ReadOnly 1 0 ∧
          ∃ (h : (ZMod p)[X]) (ρ : AdjoinRoot h), IsTransformPair p (p ^ j) h ρ ∧
            ∀ i < (tableWords p (p ^ j) h ρ).length,
              s.wmem (i + 1) = (tableWords p (p ^ j) h ρ).getD i 0 := by sorry

end CharPSComp
