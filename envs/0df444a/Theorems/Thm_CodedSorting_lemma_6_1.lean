-- Prove2me | Theorems.Thm_CodedSorting_lemma_6_1
-- name    : CodedSorting.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:03.225964+00:00
-- url     : https://prove2.me/theorems/95790ad0-9c0e-4ed5-b197-b087f92754dd
-- title:
--   Lemma 6.1 — address-field interchange of width $u$ in $O(1+\frac{V}{Bw}[1+(u/a)^{\tau}])$ block transfers
-- statement:
--   There is an absolute constant $C_{\mathrm{abs}}$ with the following property. Let $N\ge2$, $B\ge1$, $\max\{2B,C_{\mathrm{abs}}\}\le M\le N$, $w=\Theta(\log N)$, $u\ge1$, and let $P,G,\ell\ge1$ with $V=PG\ell2^{2u}$ bounded by a fixed polynomial in $N$. Then an address-field interchange of width $u$ on a bit array of $V$ bits, moving the bit at $(p,t,g,d,z)$ to $(p,d,g,t,z)$, takes at most
--   $$O\Big(1+\frac{V}{Bw}\Big[1+\Big(\frac ua\Big)^{\tau}\Big]\Big)\tag{14}$$
--   block transfers, with $a=\log_2(M/B)$, $\tau=1-\varepsilon$, $\varepsilon=3/200000$, and uses at most $M$ words of memory. The algorithm is deterministic, its execution steps are determined by the array dimensions alone, independently of the stored values, and its disk workspace is polynomial in $N$.
--
--   This is the step where the coding advantage enters: the naive recursion would give exponent $1$ in place of $\tau$.
--
--   **Formalization Note** The bit array is stored contiguously on the word disk and the result is written to the same bits. Obliviousness is the clause that the trace of actions (each transfer with its block and offset, and the halting step) is the same for all bit arrays. $C_{\mathrm{abs}}$ is chosen first; then the $\Theta$-constants $c_1,c_2$ and the polynomial degree $d$ of $V\le N^d$; then $C,k$.
--
--   Differences from the source:
--   - reading: the external-memory model of §3.1 (p.4) and Appendix D (p.39), described in prose → words `Fin (2^w)`, memory `Fin M → Word w`, disk `ℕ → Word w` with aligned blocks of $B$ words; each step applies an arbitrary memory map and one action (read a block into memory words $[o,o+B)$, write such a range to a block, nothing, or halt); every read and write is one block transfer; the step index $t$ is visible to every program; reason: the paper fixes no formal machine and this is its stated model; the step index carries no input data (every run is at step $t$ at time $t$) and is the only state Appendix D places outside the $M$ words; the program is chosen after $(N,M,B,w)$ and before the input, as p.4 says
--   - reading: $w=\Theta(\log N)$, with $O(\cdot)$ and polynomial-space constants independent of $N,M,B$ → for all $c_1>0$ and $c_2$ there are $C,k$ such that every instance with $c_1\log_2 N\le w\le c_2\log_2 N$ satisfies the bounds; reason: the hidden constants may depend on the $\Theta$-constants and on nothing else (Appendix D, p.39: "The threshold depends only on the construction and the constants in $w=\Theta(\log N)$"); this is the strongest reading
--   - reading: input, output and intermediate data on disk occupy $O(N^k)$ words → every disk block touched by a read or write lies below word $C\cdot N^k$; reason: only transferred blocks can be read or changed, and the input lies in words $0,\dots,N-1$
--   - encoding: "a bit array stored contiguously on disk" (p.18) → bit $j$ is bit $j\bmod w$ of disk word $\lfloor j/w\rfloor$, the rest of the disk and the memory are $0$, and the interchanged array is in the same bits; reason: contiguous storage on a disk of $w$-bit words
--   - reading: "the array dimensions are bounded by a fixed polynomial in the global input size $N$" (p.19) → $V\le N^d$, with $d$ quantified after $C_{\mathrm{abs}}$ and before $C,k$; reason: each of $P,G,\ell,2^u$ is at most $V$
--   - reading: "its execution steps are determined entirely by the array dimensions, independently of the stored values" → the action trace is the same for all bit arrays of the given dimensions; reason: the actions are the execution steps visible to the machine
--   - reading: "all dimension parameters and disk addresses occupy a constant number of machine words" → no separate clause; reason: it follows from $V\le N^d$ and $w\ge c_1\log_2 N$, and the program is fixed per dimension tuple
--   - reading: the main-text proof assumes $M/B$ large; Lemma A.2 and Corollary A.3 extend it → every $\max\{2B,C_{\mathrm{abs}}\}\le M\le N$; reason: the lemma states this range; $M\le N$, $N\ge2$ are the standing assumptions of §3.1
--   - encoding: $O(\cdot)$ bound → a single constant $C$ multiplying the expression; reason: the expression is at least $1$ under the hypotheses, so this is the meaning of $O(\cdot)$
--   - encoding: the algorithm sorts → there is a step $T$ at which the run has halted; reason: halting is implicit in "sorted"; no time bound is stated or added
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), Lemma 6.1, p.19 (PDF 20)

import Mathlib
import Definitions.Def_CodedSorting_Machine
import Definitions.Def_CodedSorting_BitArray
import Definitions.Def_CodedSorting_Exponent

namespace CodedSorting

/-- **Lemma 6.1 (Block transfers for address-field interchange)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), p.19.

There is an absolute constant `C_abs` such that, for `M ≥ max{2B, C_abs}`, an address-field
interchange of width `u ≥ 1` on an array of `V = PGℓ2^{2u}` bits takes at most
`O(1 + (V/(Bw)) [1 + (u/a)^τ])` block transfers, `a = log(M/B)`, `τ = 1 − ε`, `ε = 3/200000`, and
uses at most `M` words of memory. The algorithm is deterministic and its execution steps are
determined by the array dimensions alone. Its disk workspace is polynomial in `N`.

**Formalization Note.**
* The bit array is stored contiguously: bit `j` is bit `j mod w` of disk word `⌊j/w⌋`; the rest of
  the disk is `0`. Bit positions are `(p, t, g, d, z)` in lexicographic order (`bitAddr`), and the
  interchange moves the bit at `(p, t, g, d, z)` to `(p, d, g, t, z)` (`interchangeIndex`) in the same
  words.
* "Execution steps determined entirely by the array dimensions" is the clause that the action
  trace (every read/write with its block and offset, and the halting time) is the same for all
  bit arrays.
* "The array dimensions are bounded by a fixed polynomial in N" (p.19) is `V ≤ N^d`; `C_abs` is
  absolute, so it is chosen before `c₁, c₂, d`, and `C, k` after them. The standing range of §3.1
  (`N ≥ 2`, `2B ≤ M ≤ N`, `w = Θ(log N)`) is kept.
* "Dimension parameters and disk addresses occupy a constant number of machine words" is not a
  separate clause: the program is chosen per dimension tuple and needs no stored dimensions. -/
theorem lemma_6_1 :
    ∃ Cabs : ℕ, ∀ c₁ c₂ : ℝ, 0 < c₁ → ∀ d : ℕ, ∃ C : ℝ, ∃ k : ℕ,
      ∀ N M B w u P G ℓ : ℕ, 2 ≤ N → 1 ≤ B → 2 * B ≤ M → Cabs ≤ M → M ≤ N →
        c₁ * Real.logb 2 N ≤ w → (w : ℝ) ≤ c₂ * Real.logb 2 N →
        1 ≤ u → 1 ≤ P → 1 ≤ G → 1 ≤ ℓ → P * G * ℓ * 2 ^ (2 * u) ≤ N ^ d →
        ∃ prog : Program M B w,
          (∀ bits bits' : Fin (P * G * ℓ * 2 ^ (2 * u)) → Bool,
            trace prog (initCfgOf (M := M) (bitArrayDisk w bits)) =
              trace prog (initCfgOf (M := M) (bitArrayDisk w bits'))) ∧
          ∀ bits : Fin (P * G * ℓ * 2 ^ (2 * u)) → Bool, ∃ T : ℕ,
            (run prog T (initCfgOf (M := M) (bitArrayDisk w bits))).halted = true ∧
            (∀ a : Fin (P * G * ℓ * 2 ^ (2 * u)),
              readBit (run prog T (initCfgOf (M := M) (bitArrayDisk w bits))).disk
                (interchangeIndex G ℓ u a) = bits a) ∧
            ((run prog T (initCfgOf (M := M) (bitArrayDisk w bits))).ios : ℝ) ≤
              C * (1 + ((P * G * ℓ * 2 ^ (2 * u) : ℕ) : ℝ) / (B * w) *
                (1 + ((u : ℝ) / Real.logb 2 ((M : ℝ) / B)) ^ tau)) ∧
            ((run prog T (initCfgOf (M := M) (bitArrayDisk w bits))).maxEnd : ℝ) ≤
              C * (N : ℝ) ^ k := by sorry

end CodedSorting
