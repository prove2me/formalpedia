-- Prove2me | Theorems.Thm_CharPSComp_lemma_5
-- name    : CharPSComp.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T13:10:04.831866+00:00
-- url     : https://prove2.me/theorems/a1ceb9cc-da46-45d6-ac26-d920b603dfe1
-- title:
--   Lemma 5 — wide matrix multiplication: $R_{\mathrm{mat}}(k)\ge k^2$, $\log R_{\mathrm{mat}}(k)=O(\log k\,2^{\sqrt{\log k}})$, cost $O(kw2^{4\sqrt{\log k}})$
-- statement:
--   There is a computable function $R_{\mathrm{mat}}:\mathbb N\to\mathbb N$ with $R_{\mathrm{mat}}(k)\ge k^2$ for all $k$, an absolute constant $C>0$ with
--   $$\log R_{\mathrm{mat}}(k)\le C\,\log k\;2^{\sqrt{\log k}}\quad\text{for all }k,$$
--   and a construction program, an execution program and a word exponent $\kappa$ satisfying `IsWideMatMul` with the same $C$: for every admissible $M$, every commutative ring $\mathcal A$ and every $k\ge k_0=2^9$, the construction (started with $W[0]=k$) halts within $C\,R_{\mathrm{mat}}(k)$ word operations and storage, and for every $w\ge R_{\mathrm{mat}}(k)$ the execution multiplies any $A\in\mathcal A^{k\times k}$ by any $B\in\mathcal A^{k\times w}$ at cost at most $C\,kw\,2^{4\sqrt{\log k}}$, using at most $Cw$ ring cells beyond the inputs and the $kw$ output entries and at most $Cw$ word cells, leaving $S$ unwritten, with words of $O(\log R_{\mathrm{mat}}(k))$ resp. $O(\log w)$ bits.
--
--   This product at cost $2^{4\sqrt{\log k}}$ per output entry is what allows a grouped step of $\Theta((\log\log\sigma)^2)$ base-$p$ digits.
--
--   **Formalization Note** $\log$ is $\max\{1,\log_2\}$. Layout and word bounds are those of `IsWideMatMul`.
--
--   Differences from the source:
--   - reading: "explicitly computable integer-valued function" → `Computable Rmat` (Mathlib) for `Rmat : ℕ → ℕ`; reason: Mathlib's notion of a computable function
--   - reading: $\log R_{\mathrm{mat}}(k)=O((\log k)2^{\sqrt{\log k}})$ and absolute constants → one constant $C$ with $\log R_{\mathrm{mat}}(k)\le C\log k\,2^{\sqrt{\log k}}$ for every $k$, the same $C$ in the cost clauses; reason: with $\log\ge1$ an asymptotic bound with an absolute constant holds for all $k$ after enlarging the constant
--   - reading: ring operations counted in the computational model of §2.2 (additions, subtractions, multiplications in $R$; unit-cost word arithmetic and shifts) → an explicit algebraic RAM (`Instr`, `run`): unit cost per word, ring and control instruction, ring constants $k\cdot 1_R$ from words by `rint` at unit cost, no ring comparison, no ring-to-word map, no inversion or division in $R$; reason: §2.2 names the operations but no instruction set; control flow on ring values is excluded so that one program serves every ring, and `rint` is the page's convention that an integer $a$ denotes $a\cdot1_R$ (it costs $O_c(1)$ additions in fixed characteristic)
--   - reading: a fixed deterministic multiplication algorithm with cost $M(n)$ and $O(n)$ working space, $M(n)/n$ nondecreasing (§2.3) → a multiplication instruction `pmul` charged $M(\ell)$ on length $\ell$, and the statement holds for every $M$ with $\ell\le M(\ell)$ and $M(\ell)/\ell$ nondecreasing (`Admissible`); reason: the algorithm does not depend on $M$; substituting any real multiplication program for `pmul` gives the paper's statement, and every such program has $\ell\le M(\ell)$ (its $2\ell-1$ outputs need an operation each); the instruction's internal workspace is not modelled, only its $2\ell-1$ written cells are counted, which is the page's $O(\ell)$ up to a constant
--   - encoding: $\log x$ in complexity bounds → `lg x = max 1 (Real.logb 2 x)` on every logarithm, including the inner one of $\log\log$; reason: the page's own convention $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1)
--   - reading: words of $O(\log(\cdot))$ bits (§2.2) → every word value held during the run has absolute value $<(R_{\mathrm{mat}}(k)+2)^\kappa$ (construction) resp. $<(w+2)^\kappa$ (execution) for a constant $\kappa$; reason: a word of $O(\log x)$ bits holds integers of absolute value below a fixed power of $x$
--   - reading: the program "can be constructed deterministically in $O(R_{\mathrm{mat}}(k))$ word operations and words of storage" → `Build` halts at cost $\le C\,R_{\mathrm{mat}}(k)$ and writes at most $C\,R_{\mathrm{mat}}(k)$ distinct cells, leaving word cells $0,1$ unwritten; reason: the page's construction cost and storage, with space read as distinct addresses; cells $0,1$ carry $k$ and $w$ to `Exec`
--   - reading: "using $O(w)$ ring elements beyond the inputs and the $kw$ output entries" → at most $Cw$ distinct ring cells written outside the output block, and no input ring cell written; reason: the page's space count, read as distinct addresses
--   - generalization: the execution's space is stated for ring elements only → also at most $Cw$ word cells written, and $S$ and word cells $0,1$ left unwritten; reason: an added true conclusion (§2.2 counts machine words; Appendix A.3 reuses the same instructions for every batch with counters of constant number); Lemma 6 needs it to re-run the program inside $O(N)$ working space; dropping it gives the printed lemma
--   - encoding: the program $S$; MatMul → `Build`'s final word memory; `Exec` started on it with $W[1]=w$; reason: the paper's two procedures as two machine programs
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), Lemma 5 and the preceding paragraph, p.10 (PDF p.11); Appendix A.4, p.21

import Mathlib
import Definitions.Def_CharPSComp_IsWideMatMul

universe u

namespace CharPSComp

/-- Lemma 5 (Wide matrix multiplication) of Zhu, *Faster Power Series Composition in Fixed Positive
Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), p.10 (PDF p.11).

"For k₀ ≜ 2⁹, there is an explicitly computable integer-valued function Rmat(k) ≥ k² with
log Rmat(k) = O((log k) 2^{√log k}). For k ≥ k₀, the program can be constructed deterministically in
O(Rmat(k)) word operations and words of storage. Over any commutative ring A with identity, it
multiplies A ∈ A^{k×k} by B ∈ A^{k×w} for w ≥ Rmat(k) in O(kw 2^{4√log k}) ring and word
operations, using O(w) ring elements beyond the inputs and the kw output entries. All implied
constants are absolute."

**Formalization Note** "Explicitly computable" is Mathlib's `Computable`. `log` is the paper's
`max{1, log₂}` (`lg`). One absolute constant `C` serves the growth bound and every clause of
`IsWideMatMul` (construction and execution, `Def_CharPSComp_IsWideMatMul`), which also fixes the
memory layout and the word sizes stated on p.10. -/
theorem lemma_5 :
    ∃ Rmat : ℕ → ℕ, Computable Rmat ∧ (∀ k : ℕ, k ^ 2 ≤ Rmat k) ∧
      ∃ C : ℝ, 0 < C ∧ (∀ k : ℕ, lg (Rmat k) ≤ C * lg k * 2 ^ Real.sqrt (lg k)) ∧
        ∃ (Build Exec : Program) (κ : ℕ), IsWideMatMul.{u} Rmat Build Exec C κ := by sorry

end CharPSComp
