-- Prove2me | Theorems.Thm_CharPSComp_prime_power_bound
-- name    : CharPSComp.prime_power_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:02.01522+00:00
-- url     : https://prove2.me/theorems/8113be65-3e7a-4d04-87cc-79df8d65ec76
-- title:
--   §3.6.2 — composition in characteristic $p^e$ in $O_{p,e}(m+(M(n)+n\log n)\log\sigma/(\log\log\sigma)^2)$ operations and $O_{p,e}(n)$ space
-- statement:
--   Fix a prime $p$ and $e\ge1$. There are one program, a constant $C>0$ and a word exponent $\kappa$ such that for every admissible multiplication cost $M$, every nonzero commutative ring $R$ of characteristic $p^e$, all $m,n\ge1$ and all $f,g\in R[x]$ with $\deg f<m$, $\deg g<n$, with $\sigma=\min(m,n)$: the run on the input layout halts with $[x^j]f(g(x))$ in ring cell $m+n+j$ for every $j<n$, at cost at most
--   $$C\Big(m+\big(M(n)+n\log n\big)\frac{\log\sigma}{(\log\log\sigma)^2}\Big),$$
--   working space at most $Cn$, every word below $(m+n+2)^\kappa$ in absolute value, and without writing into the input.
--
--   The case $e=1$ is the prime-characteristic algorithm (end of §3.5). Chinese remaindering over the prime-power components then gives Theorem 1.
--
--   **Formalization Note** Layout: words $[m,n]$; ring cells $0,\dots,m-1$ hold $f_0,\dots,f_{m-1}$ and cells $m,\dots,m+n-1$ hold $g_0,\dots,g_{n-1}$. $\deg 0=-\infty$ (`Polynomial.degree`).
--
--   Differences from the source:
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{p,e}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $p,e$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $p,e$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(m+n+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - encoding: input $f,g$ and output $f(g(x))\bmod x^n$ → words $[m,n]$, $f$ then $g$ in ring cells $0,\dots,m+n-1$, output in cells $m+n,\dots,m+2n-1$; reason: the paper fixes no layout
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §3.6.2, last display and the two sentences after it, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible

open Polynomial

universe u

namespace CharPSComp

/-- The prime-power complexity bound of Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §3.6.2, p.17 (PDF p.18):

"T_{pᵉ}(m, n) = O_{p,e}(m + (M(n) + n log n) log σ / (log log σ)²). … The working space is
O_{p,e}(n)."

For every prime `p` and `e ≥ 1` there are one program `P`, a constant `C > 0` and a word exponent
`κ` such that for every admissible `M`, every nonzero commutative ring `R` of characteristic `pᵉ`,
all `m, n ≥ 1` and all `f, g ∈ R[x]` with `deg f < m`, `deg g < n`, with `σ = min(m, n)`, the run of
`P` on the input layout halts with `[xʲ](f(g(x)))` in ring cell `m + n + j` for every `j < n`, at
cost `≤ C (m + (M(n) + n log n) log σ / (log log σ)²)`, working space `≤ C n`, every word of
absolute value `< (m + n + 2)^κ`, and without writing into the input.

**Formalization Note** Same machine, layout and conventions as `theorem_1`: words `[m, n]`; ring
cells `0, …, m − 1` hold `f₀, …, f_{m−1}` and cells `m, …, m + n − 1` hold `g₀, …, g_{n−1}`; `log` is
the paper's `max{1, log₂}`, applied to every logarithm; `e = 1` is the prime case (§3.5). -/
theorem prime_power_bound (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) :
    ∃ (P : Program) (C : ℝ) (κ : ℕ), 0 < C ∧
      ∀ M : ℕ → ℕ, Admissible M →
      ∀ (R : Type u) [CommRing R] [Nontrivial R] [CharP R (p ^ e)],
      ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ f g : R[X], f.degree < m → g.degree < n →
        ∃ steps : ℕ,
          let s := run M P
            (initState [(m : ℤ), (n : ℤ)]
              ((List.range m).map f.coeff ++ (List.range n).map g.coeff)) steps
          s.halted = true ∧
          (∀ j < n, s.rmem (m + n + j) = (f.comp g).coeff j) ∧
          (s.cost : ℝ) ≤ C * ((m : ℝ) + ((M n : ℝ) + n * lg n) * lg (min m n : ℕ)
              / (lg (lg (min m n : ℕ))) ^ 2) ∧
          (s.space : ℝ) ≤ C * n ∧
          s.maxWord < (m + n + 2) ^ κ ∧
          s.ReadOnly 2 (m + n) := by sorry

end CharPSComp
