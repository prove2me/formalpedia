-- Prove2me | Theorems.Thm_CharPSComp_lemma_6
-- name    : CharPSComp.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:48.176475+00:00
-- url     : https://prove2.me/theorems/ffaaea71-98af-483f-8996-1b6d86f0a8b2
-- title:
--   Lemma 6 — cost of a level merge: $O_{p,C}(M(n)+N\chi\log d\log\log d)$ operations, $O_{p,C}(N)$ space
-- statement:
--   Fix a prime $p$, $C>0$, and data $(R_{\mathrm{mat}},\mathrm{Build},\mathrm{Exec},C_5,\kappa_5)$ satisfying the conclusion of Lemma 5 (`IsWideMatMul`). There are one merge program, a constant $C'>0$ and a word exponent $\kappa$ such that for every admissible $M$, every nonzero commutative ring $R$ of characteristic $p$, every $n\ge1$ with $N=p^{\lceil\log_pn\rceil}$, all admissible transform data $(h,\rho)$ for $N$ (as the table $\mathcal T$), all $k=p^a$, $w=p^b$, $v$ with $kwv=N$ and $k\le Cw$, and all input arrays (the $kw$ children $J_{kw,\cdot}\in R[z]_{<v}$ and the $k$ shared powers $G_r\in R[x]_{<kv}$):
--
--   1. with the row–column formula ($\chi=k$, flag $0$), and
--   2. with the program $S$ of Lemma 5 in memory, when $k\ge k_0=2^9$ and $w\ge R_{\mathrm{mat}}(k)$ ($\chi=2^{4\sqrt{\log_2k}}$, flag $1$),
--
--   Algorithm 1 runs to completion, writing the parent answers $J_{w,t}=\sum_{j<k}x^jC_{j,t}(x^k)$ with $C=AH\bmod z^v$ ($A$ built from the $G_r$, $H_{r,t}$ = child $t+wr$), at cost at most $C'\big(M(n)+N\chi\log d\log\log d\big)$, working space at most $C'N$, every word below $(n+2)^\kappa$, without writing into the input (in case 2 including $S$).
--
--   With (2) this charges one level of the Frobenius recursion; summing over levels gives the prime-characteristic bound.
--
--   **Formalization Note** Layout: words $[n,N,k,w,v,\mathrm{flag}]$, then $\mathcal T$, then in case 2 the word memory $S$ left by `Build`; ring cells $iv+c$ hold child $i$, cells $kwv+r\,kv+c$ hold $G_r$, and $J_{w,t}$ is written from cell $kwv+k\cdot kv+t\cdot kv$. $\log$ in the bound is $\max\{1,\log_2\}$; $\chi$ uses $\log_2$ as printed.
--
--   Differences from the source:
--   - generalization: a cost and space bound for Algorithm 1 → the same bounds plus the output clause $J_{w,t}=\sum_jx^jC_{j,t}(x^k)$ for arbitrary input arrays; reason: an added true conclusion (Algorithm 1 computes this, §3.4 and (5)); dropping it gives the printed lemma
--   - generalization: "for a fast matrix product, the program of Lemma 5" → any $(R_{\mathrm{mat}},\mathrm{Build},\mathrm{Exec},C_5,\kappa_5)$ satisfying `IsWideMatMul`, fixed before the merge program and $C'$; reason: Lemma 5's program is one such datum (its constants are absolute), and the predicate carries everything the merge uses of it, including the word-cell clauses
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - reading: $O_{p,C}(\cdot)$ bounds → one program and constants $C,\kappa$ chosen after $p,C$ and before $M$, the ring and the inputs; reason: the hidden constants may depend on $p,C$ only (footnote 1 for $O_c$); one program for all inputs is the paper's uniform algorithm, not a circuit family
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: working space counts stored ring elements and machine words beyond the read-only input → the number of distinct word addresses plus distinct ring addresses written during the run, and no input cell is ever written (`ReadOnly`); reason: §2.2 read strictly; counting every address ever written is at least the peak storage
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(n+2)^\kappa$ for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - encoding: the inputs of Algorithm 1 ($k,w,v$, $J_{kw,*}$, $G_w$, $\mathcal T$, $S$) → the word and ring layout above; $k,w$ powers of $p$; reason: the widths of the recursion are powers of $p$; the lemma fixes no layout
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 6 and the definition of χ, p.12 (PDF p.13); Algorithm 1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_CharPSComp_run
import Definitions.Def_CharPSComp_Admissible
import Definitions.Def_CharPSComp_tableWords
import Definitions.Def_CharPSComp_IsWideMatMul

open Polynomial

universe u

namespace CharPSComp

/-- Lemma 6 (Cost of a level merge) of Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.12 (PDF p.13), for
Algorithm 1 (MergeLevel, p.11).

"Put χ ≜ k for matrix products by the row–column formula and χ ≜ 2^{4√log₂ k} when the program of
Lemma 5 is available with k ≥ k₀ and w ≥ Rmat(k). Lemma 6. Given the shared powers, T and, for a
fast matrix product, the program of Lemma 5, suppose k ≤ Cw for a fixed C. Then Algorithm 1 takes
O_{p,C}(M(n) + Nχ log d log log d) operations and O_{p,C}(N) working space."

For each prime `p`, each `C > 0` and each `(Rmat, Build, Exec, C₅, κ₅)` satisfying the conclusion
of Lemma 5, there are one merge program, a constant `C'` and a word exponent `κ` such that for every
admissible `M`, every nonzero commutative ring `R` of characteristic `p`, every `n ≥ 1`, all
transform data `(h, ρ)` for `N = p^{⌈log_p n⌉}`, all `k = pᵃ`, `w = pᵇ`, `v` with `kwv = N` and
`k ≤ Cw`, and all input arrays (the `kw` children `J_{kw,·} ∈ R[z]_{<v}` and the `k` powers
`G_r ∈ R[x]_{<kv}`):
1. with flag `0` (row–column formula, `χ = k`), and
2. with flag `1` and the program `S` of Lemma 5 in memory, when `k ≥ 2⁹` and `w ≥ Rmat(k)`
   (`χ = 2^{4√log₂ k}`),
the run halts with the parent array `J_{w,t} = Σ_{j<k} xʲ C_{j,t}(xᵏ)`, `C = A H mod zᵛ`, at cost
`≤ C'(M(n) + Nχ log d log log d)`, working space `≤ C' N`, words `< (n + 2)^κ`, without writing into
the input (in case 2 including `S`).

**Formalization Note** Layout: words `[n, N, k, w, v, flag] ++ tableWords p N h ρ` (the table `T`
of Lemma 3), and in case 2 `Build`'s final word memory `S` placed right after them; ring cells
`i·v + c` (`i < kw`, `c < v`) hold child `i`, cells `kwv + r·kv + c` (`r < k`, `c < kv`) hold
`G_r`, and the output `J_{w,t}` (`kv` coefficients) is written from cell `kwv + k·kv + t·kv`.
`H_{r,t}` is child `t + wr`, as in Algorithm 1, line 1. Correctness is stated for arbitrary input
arrays. `log` in the bound is the paper's `max{1, log₂}`; `χ` uses `log₂` as printed. -/
theorem lemma_6 (p : ℕ) [Fact p.Prime] (C : ℝ) (hC : 0 < C)
    (Rmat : ℕ → ℕ) (Build Exec : Program) (C₅ : ℝ) (κ₅ : ℕ)
    (h5 : IsWideMatMul.{u} Rmat Build Exec C₅ κ₅) :
    ∃ (Pm : Program) (C' : ℝ) (κ : ℕ), 0 < C' ∧
      ∀ M : ℕ → ℕ, Admissible M → ∀ (R : Type u) [CommRing R] [Nontrivial R] [CharP R p],
      ∀ n : ℕ, 1 ≤ n →
      ∀ (h : (ZMod p)[X]) (ρ : AdjoinRoot h), IsTransformPair p (Npow p n) h ρ →
      ∀ a b v : ℕ, p ^ a * p ^ b * v = Npow p n → ((p ^ a : ℕ) : ℝ) ≤ C * (p ^ b : ℕ) →
      ∀ child pw : ℕ → ℕ → R,
      let N := Npow p n
      let k := p ^ a
      let w := p ^ b
      let d := dpar p N
      let lay : ℤ → List ℤ := fun flag =>
        [(n : ℤ), (N : ℤ), (k : ℤ), (w : ℤ), (v : ℤ), flag] ++ tableWords p N h ρ
      let rIn : List R :=
        (List.range (k * w)).flatMap (fun i => (List.range v).map (child i))
          ++ (List.range k).flatMap (fun r => (List.range (k * v)).map (pw r))
      let outOK : State R → Prop := fun s =>
        ∀ t < w, ∀ i < k * v,
          s.rmem (k * w * v + k * (k * v) + t * (k * v) + i)
            = (mergeOut k v w (fun r => polyOf (pw r) (k * v)) (fun c => polyOf (child c) v) t).coeff i
      (∃ steps : ℕ,
        let s := run M Pm (initState (lay 0) rIn) steps
        s.halted = true ∧ outOK s ∧
        (s.cost : ℝ) ≤ C' * (M n + N * (k : ℝ) * lg d * lg (lg d)) ∧
        (s.space : ℝ) ≤ C' * N ∧
        s.maxWord < (n + 2) ^ κ ∧
        s.ReadOnly (lay 0).length rIn.length) ∧
      (2 ^ 9 ≤ k → Rmat k ≤ w →
        ∀ kB : ℕ, (run M Build (initState [(k : ℤ)] ([] : List R)) kB).halted = true →
        let sB := run M Build (initState [(k : ℤ)] ([] : List R)) kB
        ∃ steps : ℕ,
          let s := run M Pm
            (mkState (fun i => if i < (lay 1).length then (lay 1).getD i 0
                else sB.wmem (i - (lay 1).length))
              (fun i => rIn.getD i 0)
              (max (((lay 1).map Int.natAbs).foldr max 0) sB.maxWord)) steps
          s.halted = true ∧ outOK s ∧
          (s.cost : ℝ) ≤ C' * (M n + N * (2 : ℝ) ^ (4 * Real.sqrt (Real.logb 2 k))
            * lg d * lg (lg d)) ∧
          (s.space : ℝ) ≤ C' * N ∧
          s.maxWord < (n + 2) ^ κ ∧
          s.ReadOnly (lay 1).length rIn.length ∧
          (∀ x ∈ s.wWritten, ∀ y ∈ insert 0 sB.wWritten, x ≠ (lay 1).length + y)) := by sorry

end CharPSComp
