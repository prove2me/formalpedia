-- Prove2me | Theorems.Thm_CharPSComp_theorem_1
-- name    : CharPSComp.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:09:05.758204+00:00
-- url     : https://prove2.me/theorems/ea69e7f8-cb3b-4869-907b-9a9ed7e232c2
-- title:
--   Theorem 1 — $f(g(x))\bmod x^n$ in $O_c(m+(M(n)+n\log n)\log\sigma/(\log\log\sigma)^2)$ ring operations and $O_c(n)$ space in characteristic $c\ge2$
-- statement:
--   Fix an integer $c\ge2$. There are one program $P$, a constant $C>0$ and a word exponent $\kappa$ such that for every admissible multiplication cost $M$, every nonzero commutative ring $R$ with identity of characteristic $c$, all positive integers $m,n$ and all $f,g\in R[x]$ with $\deg f<m$ and $\deg g<n$, putting $\sigma\triangleq\min(m,n)$: the run of $P$ on the input layout halts with $[x^j]\,f(g(x))$ in ring cell $m+n+j$ for every $j<n$ (that is, it computes $f(g(x))\bmod x^n$ deterministically), at cost at most
--   $$C\Big(m+\big(M(n)+n\log n\big)\frac{\log\sigma}{(\log\log\sigma)^2}\Big),$$
--   with working space at most $Cn$, every word of absolute value below $(m+n+2)^\kappa$ (words of $O(\log(m+n))$ bits), and without writing into the input.
--
--   For $m=n$ and $M(n)=O(n\log n)$ this is $O_c(n\log^2n/(\log\log n)^2)$, improving Bernstein's $O_c(M(n)\log n)$ by a factor $(\log\log n)^2$.
--
--   **Formalization Note** The machine is `CharPSComp.run`: unit-cost ring and word operations, a polynomial-multiplication instruction charged $M(\ell)$ on length $\ell$, no ring comparison and no ring-to-word map. Layout: words $[m,n]$; ring cells $0,\dots,m-1$ hold $f_0,\dots,f_{m-1}$ and cells $m,\dots,m+n-1$ hold $g_0,\dots,g_{n-1}$. $\log$ is $\max\{1,\log_2\}$, so $\log\log\sigma\ge1$. $\deg0=-\infty$.
--
--   Differences from the source:
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{c}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $c$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $c$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(m+n+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - encoding: input $f,g$ and output $f(g(x))\bmod x^n$ → words $[m,n]$, $f$ then $g$ in ring cells $0,\dots,m+n-1$, output in cells $m+n,\dots,m+2n-1$; reason: the paper fixes no layout
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Theorem 1 with footnote 1, p.1 (PDF p.2); §2.1–2.3, pp.4–5

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible

open Polynomial

universe u

namespace CharPSComp

/-- Theorem 1 of Zhu, *Faster Power Series Composition in Fixed Positive Characteristic*, STOC 2027
submission (manuscript sha256 e63e0527…), p.1 (PDF p.2), with footnote 1:

"Fix an integer c ≥ 2, and let R be a nonzero commutative ring with identity of characteristic c.
Given positive integers m, n and polynomials f, g ∈ R[x] with deg f < m and deg g < n, put
σ ≜ min(m, n). Then f(g(x)) mod xⁿ can be computed deterministically in
O_c(m + (M(n) + n log n) log σ / (log log σ)²) ring operations and O_c(n) working space."
"The hidden constant in O_c(·) may depend on c."

For every `c ≥ 2` there are one program `P`, a constant `C > 0` and a word exponent `κ`, chosen
before everything else, such that for every admissible multiplication cost `M`, every nonzero
commutative ring `R` of characteristic `c`, all `m, n ≥ 1` and all `f, g ∈ R[x]` with `deg f < m`,
`deg g < n`: the run of `P` on the input layout halts with `[xʲ](f(g(x)))` in ring cell `m + n + j`
for every `j < n`, at cost `≤ C (m + (M(n) + n log n) log σ / (log log σ)²)`, working space
`≤ C n`, every word of absolute value `< (m + n + 2)^κ` (words of `O(log(m + n))` bits), and
without writing into the input.

**Formalization Note** The machine is `Def_CharPSComp_run` (§2.2): unit-cost ring and word
operations, a polynomial-multiplication instruction charged `M(ℓ)` on length `ℓ`, no ring
comparison and no ring-to-word map. `M` ranges over `Admissible` costs (`ℓ ≤ M(ℓ)`, `M(ℓ)/ℓ`
nondecreasing; §2.3). Layout: words `[m, n]`; ring cells `0, …, m − 1` hold `f₀, …, f_{m−1}` and
cells `m, …, m + n − 1` hold `g₀, …, g_{n−1}`; these cells are read-only. Working space counts the
distinct word and ring addresses written. `log` is the paper's `max{1, log₂}` (§2.1), applied to
every logarithm, so `log log σ ≥ 1`. `deg 0 = −∞` (`Polynomial.degree`). -/
theorem theorem_1 :
    ∀ c : ℕ, 2 ≤ c →
    ∃ (P : Program) (C : ℝ) (κ : ℕ), 0 < C ∧
      ∀ M : ℕ → ℕ, Admissible M →
      ∀ (R : Type u) [CommRing R] [Nontrivial R] [CharP R c],
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
