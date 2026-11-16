-- Prove2me | Theorems.Thm_DynStrings_Supplement_theorem_6_1_persistent_dynamic_strings
-- name    : DynStrings.Supplement.theorem_6_1_persistent_dynamic_strings
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:52:07.910254+00:00
-- url     : https://prove2.me/theorems/6f382eff-5baa-42b8-8a12-d450f90d1d36
-- title:
--   Theorem 6.1 — persistent dynamic strings: $O(\tau)$-time operations w.p. $1-\eta$, resident space $O(1+(\delta(\mathcal W)+|\mathcal W|)\tau(L_{\mathcal W},\eta))$, expected $O(1+D_{\mathcal W})$
-- statement:
--   Fix a word size $w\ge2$. The machine is a **word RAM** with $w$-bit words, unit-cost arithmetic (including multiplication, division and the most significant set bit), and a primitive $\mathrm{Uniform}(r)$ that returns an independent uniform element of $[0\,.\,.\,r)$ for a positive word $r$. Memory consists of blocks of any number of words, allocated uninitialized or freed in constant time. The **space** is the total size of the allocated blocks plus a constant overhead per block. The **resident space** is what is retained between operations, and the **transient space** of an operation is what it allocates and frees before returning; input and returned arrays belong to the caller.
--
--   The data structure maintains strings through handles. $\mathcal W$ is the multiset holding one copy of the string of every live handle to a non-empty string; the empty string has a constant handle. The operations are $\mathrm{Insert}(S)$, $\mathrm{Concat}(X,Y)$, $\mathrm{Split}(X,i)$, $\mathrm{Delete}(X)$, $\mathrm{Get}(X)$, $\mathrm{Equal}(X,Y)$, $\mathrm{Lcp}(X,Y)$ and $\mathrm{Ipm}(X,Y)$, where Ipm returns $\mathrm{Occ}(X,Y)=\{i: Y(i\,.\,.\,i+|X|]=X\}$ as an arithmetic progression. An operation sequence is **oblivious** (fixed in advance, independently of the random choices) and **admissible** (all characters, lengths and counts fit in a word, and fewer than $2^w$ distinct non-empty strings are live at any time). For a collection, $L_{\mathcal W}=\sum_{Z\in\mathcal W}(|Z|+1)$, $\delta(\mathcal W)$ is its substring complexity, and $D_{\mathcal W}$ is its space parameter (Definition 3.1). The tail scale is
--
--   $$\tau(m,\eta)=\lg m+\frac{\log(1/\eta)}{\lg\big(\log(1/\eta)/\lg m\big)}.$$
--
--   **Theorem.** There is a data structure, giving correct answers on every outcome of its random choices, such that for every constant $C\ge1$, every oblivious admissible sequence and every $\eta$ with $2^{-w^C}\le\eta<1$:
--
--   1. every fixed operation runs, with probability at least $1-\eta$, within $O(1+|S|\,\tau(1,\eta))$ for Insert, $O(\tau(|X|,\eta))$ for Split, $O(\tau(|X|+|Y|,\eta))$ for Concat, $O(\tau(\max\{|X|,|Y|\},\eta))$ for Lcp and Ipm, and $O((1+\delta(X\mid\mathcal C))\,\tau(|X|,\eta))$ for Delete, where $\mathcal C$ is the collection after the deletion. Get takes $O(1+|X|)$ and Equal $O(1)$, deterministically. The hidden constants may depend on $C$;
--   2. at every fixed time between two operations, the resident space is $O\big(1+(\delta(\mathcal W)+|\mathcal W|)\,\tau(L_{\mathcal W},\eta)\big)$ words with probability at least $1-\eta$;
--   3. at every such time, the union of the grammars of the current strings has expected size $O(D_{\mathcal W})$, and the expected resident space is $O(1+D_{\mathcal W})$ words;
--   4. the transient space of each operation is bounded by its running-time bound. For Get it is $O(\lg|X|)$ besides the returned array.
--
--   The data structure does not depend on $C$, $\eta$, or any bound on string lengths or on the number of operations.
--
--   This is the paper's main data-structure theorem: persistent strings stored in space close to the optimal compressed size $D_{\mathcal W}$, with updates and queries in logarithmic time with high probability.
--
--   **Formalization Note** The machine (`WordRAM`), the operations, the oblivious sequences and their execution (`DynOps`) are the supplement's definitions. Pointers are opaque. The randomness is a coin sequence with the product uniform law. Uninitialized words are arbitrary (`junk`), and every clause holds for every `junk`. The data structure declares the random orders it parses with, as a function of its coins, and the grammar clause is stated for these orders. Probabilities are bounded with the outer measure; expectations are Lebesgue integrals of a.e.-measurable functions.
--
--   Differences from the source:
--   - generalization: a word RAM whose memory addresses are words (pointer values usable as integers) → the word RAM `WordRAM` with opaque pointers to allocated blocks: pointers can be stored, copied and compared for equality, but not used in arithmetic; reason: a data structure on this machine runs unchanged on the paper's machine (a pointer is an address), so the statement specializes to the source's
--   - generalization: admissible: every input character, string length, position, array index, reference count and memory address fits in a word, for every outcome → `Admissible`: every input character and every string length is < 2^w, every string has fewer than 2^w live handles, and fewer than 2^w distinct non-empty strings are live at any time; no condition on the data structure's own memory addresses (block sizes and offsets are words by construction); reason: every sequence admissible in the paper's sense is admissible here (on the paper's machine handles are words, and live handles to distinct strings differ from each other and from the empty handle); dropping the part of the address condition that refers to the data structure's own execution admits more sequences
--   - reading: memory addresses fit in a word → the sequence-controlled part of it: fewer than 2^w distinct non-empty strings are live at every time; reason: the paper's condition refers to the data structure being asserted to exist, so as a hypothesis of an ∃-statement it lets a structure that overflows its address space make every sequence inadmissible; its consequence for the sequence alone, that distinct live strings have distinct word-sized handles, is kept, which bounds the records of the grammar union by 2^{O(w)}
--   - reading: every reference count fits in a word → at every time every string has fewer than 2^w live handles; reason: the source's reference counts are internal to its data structure; the part of them the operation sequence controls is the number of live handles of one string
--   - reading: the transient space of each operation is bounded by its running time bound; for Get(X) it is O(lg |X|) besides the returned array → for every operation, the transient space exceeds K times its time bound with probability at most η; for Get it is at most K·lg|X| and for Equal at most K on every outcome; reason: Get's and Equal's time bounds are deterministic and no probability is attached to Get's transient bound, so the deterministic reading is the stronger one
--   - reading: correct answers for every outcome of its random choices → on every coin sequence, initialization and every operation halt without a fault and return correct answers (handles of empty results are the empty handle); reason: an answer on every outcome requires the operation to finish; this is the stronger of the two readings
--   - reading: the union of the grammars of the current strings → the RLSLP size of the union of the base `grammar`s of the strings of W under the orders `D.orders ω` that the data structure declares as a function of its coins, required to satisfy `IsRandomOrders` under the coin law; reason: the paper's data structure parses all strings with random orders drawn from its own random choices (§7); the Lean statement does not relate the stored records to these grammars
--   - encoding: Uniform(r) returns an independent uniform element of [0 . . r) → a coin sequence ω ∈ [0,1]^ℕ with the product uniform law; the c-th draw with bound r is min(⌊ω_c·r⌋, r − 1); reason: the same law: independent and uniform on [0 . . r)
--   - encoding: blocks are allocated uninitialized → a new block holds arbitrary words `junk b o`; every clause holds for every `junk`; reason: uninitialized means unspecified contents
--   - encoding: space = total size of the allocated blocks plus a constant overhead per block → `Mem.space`: ∑ (size + 1) over the live blocks of the data structure; reason: any fixed overhead constant changes only the hidden constants
--   - encoding: handles; an oblivious sequence fixed in advance, independent of the random choices → a fixed `σ : List Op` whose handle arguments are `HRef.out t j` (output j of operation t) or `HRef.empty`; the harness substitutes the handle values the data structure returned; reason: handle values depend on the execution, so a sequence fixed in advance names them by their creation
--   - encoding: input arrays and returned arrays belong to the caller and are not counted → Insert(S) receives a read-only caller block holding S; Get(X) returns a pointer to a block of |X| words holding X, which is then handed to the caller; caller blocks are never counted as space; reason: the calling convention of §6.2
--   - encoding: Ipm returns the arithmetic progression Occ(X, Y) by first position, offset and count → three words f, d, c with c = |Occ(X, Y)| and Occ(X, Y) = {f + j·d : j < c}; reason: exactly the returned progression
--   - encoding: running time; resident space between operations; transient space = space allocated and freed before returning → the number of executed steps; `Mem.space` after initialization and the first s operations; the largest total (size + 1), over the steps of the operation, of the blocks it allocates and frees before it returns; reason: the definitions of §6.2 and App. A.1 for one execution
--   - encoding: the hidden constants of the table may depend on C; the expected bounds O(D_W) and O(1 + D_W) → ∀ C ≥ 1, ∃ K > 0 before w, junk, σ and η for the table, the w.h.p. space and transient clauses; one absolute K₀ for the two expected bounds; reason: the expected bounds do not involve C
--   - encoding: with probability at least 1 − η; expected size → the outer measure of the bad event is at most η; a lower Lebesgue integral of an a.e.-measurable function; reason: the bad-event form does not need measurability; the measurability conjunct makes the integral the expectation
--   - encoding: the data structure starts empty → an initialization program run once before the first operation, with no time bound; s = 0 is the time after it; reason: the source's structure has an initial empty state, and 'every fixed time between two operations' includes the time before the first one
--   - encoding: characters of an alphabet that fit in a word → strings `List ℕ` with characters < 2^w (part of `Admissible`); reason: the input characters are words
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Theorem 6.1, p.29 (PDF p.30); model §6.1–6.2, pp.27–29; App. A.1, pp.58–59; Definition 3.1, p.14; Eq. (3), p.20

import Mathlib
import Definitions.Def_DynStrings_Supplement_DynOps
open MeasureTheory ProbabilityTheory

namespace DynStrings.Supplement

open DynStrings

/-- **Theorem 6.1** (Persistent dynamic strings), p.29.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There is a data structure supporting the operations of §6.1, with correct answers for every outcome
of its random choices, such that the following holds for every constant `C ≥ 1`. Fix an oblivious
admissible operation sequence and `η` with `2^{−w^C} ≤ η < 1`. For every fixed operation, its running
time is bounded as follows with probability at least `1 − η` (hidden constants depending on `C`):
`Insert(S)`: `O(1 + |S| τ(1, η))`; `Split(X, i)`: `O(τ(|X|, η))`; `Concat(X, Y)`:
`O(τ(|X| + |Y|, η))`; `Lcp(X, Y)`, `Ipm(X, Y)`: `O(τ(max{|X|, |Y|}, η))`; `Delete(X)`:
`O((1 + δ(X | C)) τ(|X|, η))` with `C` the collection after the deletion; `Get(X)`: `O(1 + |X|)`
deterministically; `Equal(X, Y)`: `O(1)` deterministically. At every fixed time between two
operations, the resident space is `O(1 + (δ(W) + |W|) τ(L_W, η))` words with probability at least
`1 − η`; the union of the grammars of the current strings has expected size `O(D_W)`, and the
expected resident space is `O(1 + D_W)` words. The transient space of each operation is bounded by
its running time bound; for `Get(X)` it is `O(lg |X|)` besides the returned array. The data
structure does not depend on `C`, `η`, or any bound on string lengths or on the number of
operations.

**Formalization Note.**
* The data structure `D` is chosen first, so it does not depend on `C`, `η`, the word size, the
  sequence or any bound. The machine is the word RAM of `WordRAM` (unit-cost word operations,
  `Uniform(r)` for words `r`, allocated blocks with opaque pointers), the execution and the
  measures of time and space are those of `DynOps`; uninitialized memory holds arbitrary words
  `junk`, and every clause holds for every `junk`.
* Correctness: for every word size `w ≥ 2`, every well-formed admissible sequence and every coin
  sequence `ω`, initialization and every operation halt without a fault and answer correctly.
* The declared orders of `D` are random orders in the sense of §4.2 under the coin law, and the
  expected RLSLP size of the union of the grammars of the strings of `W` under these orders is at
  most `K₀ D_W`; the expected resident space is at most `K₀ (1 + D_W)`. `K₀` is absolute.
* For every `C ≥ 1` there is `K` such that, for every `w ≥ 2`, every well-formed admissible sequence
  and every `η` with `2^{−w^C} ≤ η < 1` (the exponent is `−(w^C)`, as printed on p.29): every fixed
  operation exceeds `K` times its time bound (`timeBound`) with probability at most `η`, and so does its transient space; `Get` and `Equal`
  meet their time bounds on every outcome, and `Get`'s transient space is at most `K lg |X|` on every
  outcome; at every fixed time `s ∈ [0, |σ|]`, the resident space exceeds
  `K (1 + (δ(W) + |W|) τ(L_W, η))` with probability at most `η`.
* Probabilities are bounded with the outer measure, expectations are lower Lebesgue integrals of
  a.e.-measurable functions. -/
theorem theorem_6_1_persistent_dynamic_strings :
    ∃ D : DataStructure,
      (∀ w : ℕ, 2 ≤ w → ∀ (junk : ℕ → ℕ → BitVec w) (σ : List Op), WellFormed σ →
        Admissible w σ → ∀ ω : Coins,
          (initState D junk ω).isSome ∧
          ∀ (s : ℕ) (o : Op), σ[s]? = some o →
            ∃ r, opResult D junk σ ω s = some r ∧ AnswerOK D σ r o) ∧
      IsRandomOrders coinLaw (fun k ω => D.orders ω k) ∧
      (∃ K₀ : ℝ, 0 < K₀ ∧
        ∀ w : ℕ, 2 ≤ w → ∀ (junk : ℕ → ℕ → BitVec w) (σ : List Op), WellFormed σ →
          Admissible w σ → ∀ s ≤ σ.length,
            (AEMeasurable (fun ω => (unionSize D σ s ω : ENNReal)) coinLaw ∧
              ∫⁻ ω, (unionSize D σ s ω : ENNReal) ∂coinLaw ≤
                ENNReal.ofReal (K₀ * DColl (coll σ s))) ∧
            (AEMeasurable (fun ω => resident D junk σ ω s) coinLaw ∧
              ∫⁻ ω, resident D junk σ ω s ∂coinLaw ≤
                ENNReal.ofReal (K₀ * (1 + DColl (coll σ s))))) ∧
      ∀ C : ℝ, 1 ≤ C → ∃ K : ℝ, 0 < K ∧
        ∀ w : ℕ, 2 ≤ w → ∀ (junk : ℕ → ℕ → BitVec w) (σ : List Op), WellFormed σ →
          Admissible w σ → ∀ η : ℝ, (2 : ℝ) ^ (-((w : ℝ) ^ C)) ≤ η → η < 1 →
            (∀ (s : ℕ) (o : Op), σ[s]? = some o →
              coinLaw {ω | ENNReal.ofReal (K * timeBound σ s η o) < opTime D junk σ ω s} ≤
                ENNReal.ofReal η ∧
              coinLaw {ω | ENNReal.ofReal (K * timeBound σ s η o) < opTransient D junk σ ω s} ≤
                ENNReal.ofReal η ∧
              (∀ x, o = .get x → ∀ ω,
                opTime D junk σ ω s ≤ ENNReal.ofReal (K * (1 + (str σ x).length)) ∧
                opTransient D junk σ ω s ≤ ENNReal.ofReal (K * lg (str σ x).length)) ∧
              (∀ x y, o = .equal x y → ∀ ω,
                opTime D junk σ ω s ≤ ENNReal.ofReal K ∧
                opTransient D junk σ ω s ≤ ENNReal.ofReal K)) ∧
            ∀ s ≤ σ.length,
              coinLaw {ω | ENNReal.ofReal (K * (1 + (deltaColl (coll σ s) +
                  (Multiset.card (coll σ s) : ℝ)) * tau (LColl (coll σ s)) η)) <
                resident D junk σ ω s} ≤ ENNReal.ofReal η := by sorry

end DynStrings.Supplement
