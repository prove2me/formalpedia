-- Prove2me | Theorems.Thm_CharPSComp_lemma_2
-- name    : CharPSComp.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:08:58.241471+00:00
-- url     : https://prove2.me/theorems/66fa8331-0e19-42f8-836a-8c4eb8df7302
-- title:
--   Lemma 2 — products of bounded total length in $O_C(M(n))$ operations and $O_C(n)$ space
-- statement:
--   Fix $C>0$. There are one program, a constant $C'>0$ and a word exponent $\kappa$ such that for every admissible multiplication cost $M$, every nonzero commutative ring $R$, every $n\ge1$, all $t$ and positive lengths $\ell_1,\dots,\ell_t$ with $\sum_i\ell_i\le Cn$, and all $A_i,B_i\in R[x]_{<\ell_i}$: the run on the input layout halts with the $2\ell_i-1$ coefficients of every product $A_iB_i$ written separately, at cost at most $C'M(n)$, working space at most $C'n$, every word below $(n+t+2)^\kappa$ in absolute value, without writing into the input.
--
--   This lemma is what charges all the convolutions of the transforms and all the successive powers of the inner polynomial $O(M(n))$ per level.
--
--   **Formalization Note** Indices are $0$-based. Layout: words $[n,t,\ell_0,\dots,\ell_{t-1}]$; ring memory holds $A_0,B_0,A_1,B_1,\dots$ (each of length $\ell_i$) from cell $0$; $A_iB_i$ is written from cell $2\sum\ell+\sum_{i'<i}(2\ell_{i'}-1)$.
--
--   Differences from the source:
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{C}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $C$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $C$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(n+t+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - encoding: given $A_i,B_i$ → input and output layout in the machine's memories; reason: the lemma fixes no layout
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible
import Definitions.Def_CharPSComp_J

open Polynomial

universe u

namespace CharPSComp

/-- Lemma 2 (Products of bounded total length) of Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.8 (PDF p.9).

Let `ℓ_1, …, ℓ_t` be positive integers with `Σ ℓ_i ≤ Cn` for a fixed `C > 0`. Given
`A_i, B_i ∈ R[x]_{<ℓ_i}`, all `A_iB_i` can be computed separately in `O_C(M(n))` operations and
`O_C(n)` working space.

On the machine of `Def_CharPSComp_run`: for each `C > 0` there are one program `P`, a constant `C'`
and a word exponent `κ` such that for every admissible `M`, every nonzero commutative ring `R`,
every `n ≥ 1` and all such lengths and inputs, the run halts with the coefficients of every
`A_iB_i` in place, at cost `≤ C' M(n)`, working space `≤ C' n`, words `< (n + t + 2)^κ`, without
writing into the input.

**Formalization Note** Layout: words `W = [n, t, ℓ_0, …, ℓ_{t−1}]`; ring memory holds the
coefficient arrays `A_0, B_0, A_1, B_1, …` (each of length `ℓ_i`) from cell `0`; the product
`A_iB_i` (`2ℓ_i − 1` coefficients) is written from cell `2Σ_i ℓ_i + Σ_{i'<i}(2ℓ_{i'} − 1)`.
Indices are `0`-based. -/
theorem lemma_2 (C : ℝ) (hC : 0 < C) :
    ∃ (P : Program) (C' : ℝ) (κ : ℕ), 0 < C' ∧
      ∀ M : ℕ → ℕ, Admissible M → ∀ (R : Type u) [CommRing R] [Nontrivial R],
      ∀ (n t : ℕ) (ℓ : ℕ → ℕ), 1 ≤ n → (∀ i < t, 1 ≤ ℓ i) →
        ((∑ i ∈ Finset.range t, ℓ i : ℕ) : ℝ) ≤ C * n →
      ∀ A B : ℕ → ℕ → R,
        ∃ steps : ℕ,
          let s := run M P
            (initState ([(n : ℤ), (t : ℤ)] ++ (List.range t).map (fun i => (ℓ i : ℤ)))
              ((List.range t).flatMap
                (fun i => (List.range (ℓ i)).map (A i) ++ (List.range (ℓ i)).map (B i)))) steps
          s.halted = true ∧
          (∀ i < t, ∀ c < 2 * ℓ i - 1,
            s.rmem (2 * (∑ i' ∈ Finset.range t, ℓ i')
                + (∑ i' ∈ Finset.range i, (2 * ℓ i' - 1)) + c)
              = (polyOf (A i) (ℓ i) * polyOf (B i) (ℓ i)).coeff c) ∧
          (s.cost : ℝ) ≤ C' * M n ∧
          (s.space : ℝ) ≤ C' * n ∧
          s.maxWord < (n + t + 2) ^ κ ∧
          s.ReadOnly (t + 2) (2 * ∑ i ∈ Finset.range t, ℓ i) := by sorry

end CharPSComp
