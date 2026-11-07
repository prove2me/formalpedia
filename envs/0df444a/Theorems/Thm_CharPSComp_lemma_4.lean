-- Prove2me | Theorems.Thm_CharPSComp_lemma_4
-- name    : CharPSComp.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:40.106305+00:00
-- url     : https://prove2.me/theorems/0def8a66-0b6c-444f-90ef-43a8f1027226
-- title:
--   Lemma 4 — batched evaluation and interpolation on $\rho^i$ in $O_{p,C}(M(n)+N\log d\log\log d)$
-- statement:
--   Fix a prime $p$ and $C>0$. There are an evaluation program, an interpolation program, a constant $C'>0$ and a word exponent $\kappa$ such that for every admissible $M$, every nonzero commutative ring $R$ of characteristic $p$, every $n\ge1$ (with $N=p^{\lceil\log_pn\rceil}$ and $d$ as in Table 1), all admissible transform data $(h,\rho)$ for $N$ given as the table $\mathcal T$, and all $L,t$ with $1\le L\le L_{\max}$ and $tLd\le CN$:
--
--   1. **evaluation:** given the coefficients $c_{a,j}\in E$ ($a<t$, $j<L$) of $t$ polynomials $P_a(y)=\sum_{j<L}c_{a,j}y^j\in E[y]_{<L}$, the program writes the values $P_a(\rho^i)$ for $0\le i<L$;
--   2. **interpolation:** given the values $P_a(\rho^i)$, $0\le i<L$, of $t$ such polynomials, the program writes their coefficients $c_{a,j}$;
--
--   each run halting at cost at most $C'\big(M(n)+N\log d\log\log d\big)$, working space at most $C'N$, every word below $(n+2)^\kappa$, without writing into the input.
--
--   These transforms reduce one polynomial matrix product of a level merge to $L$ matrix products over $E$.
--
--   **Formalization Note** $E=R[z]/(h)$ with $h$ carried into $R[z]$; elements of $E$ are given by $d$ coordinates, and $\rho$ enters $E$ through its representative. Layout: words $[n,N,L,t]$ followed by $\mathcal T$; ring cell $aLd+jd+e$ holds coordinate $e$ of entry $j$ of polynomial $a$; the output uses the same indexing from cell $tLd$.
--
--   Differences from the source:
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{p,C}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $p,C$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $p,C$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(n+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - reading: interpolating the $t$ polynomials from their values → given the values $P_a(\rho^i)$ of polynomials of degree $<L$, output their coefficients; reason: $V_L$ is invertible by the unit clause of Lemma 3, so the coefficients are determined
--   - encoding: the data of Lemma 3 → the word table `tableWords` placed after $[n,N,L,t]$; reason: the table $\mathcal T$ of §3.3.1
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 4, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible
import Definitions.Def_CharPSComp_tableWords

open Polynomial

universe u

namespace CharPSComp

/-- Lemma 4 (Batched evaluation and interpolation) of Zhu, *Faster Power Series Composition in
Fixed Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.9 (PDF p.10).

"Given the data of Lemma 3, let 1 ≤ L ≤ L_max and tLd ≤ CN for a fixed C > 0. Evaluating t
polynomials in E[y]_{<L} at the points ρⁱ for 0 ≤ i < L, or interpolating them from these values,
takes O_{p,C}(M(n) + N log d log log d) operations and O_{p,C}(N) space."

For each prime `p` and `C > 0` there are an evaluation program, an interpolation program, a constant
`C'` and a word exponent `κ` such that for every admissible `M`, every nonzero commutative ring `R`
of characteristic `p`, every `n ≥ 1` (with `N = p^{⌈log_p n⌉}`, `d` as in Table 1), all transform
data `(h, ρ)` for `N`, and all `L, t` with `1 ≤ L ≤ L_max`, `tLd ≤ CN`:
1. (evaluation) given the coefficients `c_{a,j} ∈ E` (`a < t`, `j < L`) of `t` polynomials
   `P_a(y) = Σ_{j<L} c_{a,j} yʲ`, the evaluation program writes the values `P_a(ρⁱ)`, `i < L`;
2. (interpolation) given the values `P_a(ρⁱ)`, `i < L`, of `t` such polynomials, the interpolation
   program writes their coefficients `c_{a,j}`;
each run halts at cost `≤ C'(M(n) + N log d log log d)`, working space `≤ C' N`, words `< (n + 2)^κ`,
without writing into the input.

**Formalization Note** `E = R[z]/(h)`; an element of `E` is given by its `d` coordinates (the
coefficients of its representative of degree `< d`), and `ρ` enters `E` through its representative
with coefficients carried from `F_p` into `R` (`embedF`). Layout: words
`[n, N, L, t] ++ tableWords p N h ρ` (the table `T` of Lemma 3); ring cell `a·L·d + j·d + e` holds
coordinate `e` of the `j`-th entry of polynomial `a`; the output array uses the same indexing from
cell `tLd`. `log` is the paper's `max{1, log₂}`. -/
theorem lemma_4 (p : ℕ) [Fact p.Prime] (C : ℝ) (hC : 0 < C) :
    ∃ (Pev Pint : Program) (C' : ℝ) (κ : ℕ), 0 < C' ∧
      ∀ M : ℕ → ℕ, Admissible M → ∀ (R : Type u) [CommRing R] [Nontrivial R] [CharP R p],
      ∀ n : ℕ, 1 ≤ n →
      ∀ (h : (ZMod p)[X]) (ρ : AdjoinRoot h), IsTransformPair p (Npow p n) h ρ →
      ∀ L t : ℕ, 1 ≤ L → L ≤ Lmax p (Npow p n) →
        ((t * L * dpar p (Npow p n) : ℕ) : ℝ) ≤ C * (Npow p n : ℕ) →
      let N := Npow p n
      let d := dpar p N
      let words : List ℤ := [(n : ℤ), (N : ℤ), (L : ℤ), (t : ℤ)] ++ tableWords p N h ρ
      let layout : (ℕ → ℕ → ℕ → R) → List R := fun c =>
        (List.range t).flatMap fun a => (List.range L).flatMap fun j => (List.range d).map (c a j)
      let value : (ℕ → ℕ → ℕ → R) → ℕ → ℕ → ℕ → R := fun c a i e =>
        ((∑ j ∈ Finset.range L,
            polyOf (c a j) d * ((rep h ρ).map (ZMod.castHom (dvd_refl p) R)) ^ (i * j))
          %ₘ liftH R h).coeff e
      ∀ c : ℕ → ℕ → ℕ → R,
        (∃ steps : ℕ,
          let s := run M Pev (initState words (layout c)) steps
          s.halted = true ∧
          (∀ a < t, ∀ i < L, ∀ e < d, s.rmem (t * L * d + a * L * d + i * d + e) = value c a i e) ∧
          (s.cost : ℝ) ≤ C' * (M n + N * lg d * lg (lg d)) ∧
          (s.space : ℝ) ≤ C' * N ∧
          s.maxWord < (n + 2) ^ κ ∧
          s.ReadOnly words.length (t * L * d)) ∧
        (∃ steps : ℕ,
          let s := run M Pint (initState words (layout (value c))) steps
          s.halted = true ∧
          (∀ a < t, ∀ j < L, ∀ e < d, s.rmem (t * L * d + a * L * d + j * d + e) = c a j e) ∧
          (s.cost : ℝ) ≤ C' * (M n + N * lg d * lg (lg d)) ∧
          (s.space : ℝ) ≤ C' * N ∧
          s.maxWord < (n + 2) ^ κ ∧
          s.ReadOnly words.length (t * L * d)) := by sorry

end CharPSComp
