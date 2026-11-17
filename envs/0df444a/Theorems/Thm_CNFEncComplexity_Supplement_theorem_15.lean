-- Prove2me | Theorems.Thm_CNFEncComplexity_Supplement_theorem_15
-- name    : CNFEncComplexity.Supplement.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:36:00.194581+00:00
-- url     : https://prove2.me/theorems/5dc88763-32fa-4529-9e61-6371da010888
-- title:
--   Theorem 15 — a deterministic $O(n^2)$-bit data structure answers $u^{\mathsf T}Av$ in time $n^2/2^{\Omega(\sqrt{\lg n})}$
-- statement:
--   There are constants $c>0$, $C$ and $N_0$ and a single deterministic program $P$ of the paper's random access machine (§3.1, logarithmic cost) with the following property. For every $n\ge N_0$ and every boolean matrix $A\in\{0,1\}^{n\times n}$ there is a memory image $D$ of at most $Cn^2$ bits such that for all $u,v\in\{0,1\}^n$, the run of $P$ started with memory $D$ on the input $u$ followed by $v$ halts with output
--   $$u^{\mathsf T}Av=\bigvee_{i,j}\,(u_i\wedge A_{ij}\wedge v_j)\in\{0,1\}$$
--   (the product over the boolean semiring) at a total cost of at most
--   $$\frac{n^2}{2^{\,c\sqrt{\log_2 n}}}.$$
--
--   This is the derandomization of the Larsen–Williams data structure. Since $\mathrm{IS}_G(u,v)=1$ iff $u^{\mathsf T}Av=0$ for the biadjacency matrix $A$ of a bipartite graph $G$, it is the data structure that Theorem 2 turns into the encodings of Theorem 4.
--
--   **Formalization Note** "Deterministically" is the absence of nondeterministic jumps; the query program is one program for all $n$ and $A$, and only the memory image depends on $A$. Memory size is the total bit length of the preloaded registers; time is the logarithmic cost of the run including the halting step. Preprocessing time is not part of the statement.
--
--   Differences from the source:
--   - reading: a data structure using O(n²) bits of memory … deterministically compute uᵀAv … in time n²/2^{Ω(√lg n)} (no machine model fixed) → one fixed njump-free program of the paper's §3.1 log-cost RAM, run from a preloaded memory image D (depending on A) with memBits D ≤ C·n², on input u ++ v, halting with r₀ = uᵀAv at cost ≤ n²/2^{c√(log₂ n)}; reason: the paper's only machine model is the §3.1 RAM, and the proof of Theorem 4 feeds Theorem 15 into Theorem 2 in that model; a query algorithm is one algorithm for all n; polylog factors between log-cost and unit-cost RAMs are absorbed by 2^{Ω(√lg n)}
--   - encoding: O(n²) bits; time n²/2^{Ω(√lg n)} → ∃ C, c > 0, N₀ (absolute) with the bounds for every n ≥ N₀; reason: standard meaning of O and Ω; a leading constant in the time is absorbed by halving c
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 15, p.15 (PDF 16), proof p.17 (PDF 18); §3.1, pp.10–11 (PDF 11–12)

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_AcceptsWithin
import Definitions.Def_CNFEncComplexity_Supplement_RunsTo

namespace CNFEncComplexity.Supplement

open CNFEncComplexity

/-- **Theorem 15 (deterministic Larsen–Williams data structure).** Krapivin, Przybocki,
Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version,
sha256 97421ce1…), Theorem 15, p.15 (PDF 16), proof p.17 (PDF 18): "For every boolean matrix
A ∈ {0, 1}^{n×n}, there is a data structure using O(n²) bits of memory for which, given
u, v ∈ {0, 1}ⁿ, one can deterministically compute uᵀAv over the boolean semiring in time
n²/2^{Ω(√lg n)}."

There are constants `c > 0`, `C`, `N₀` and one program `prog` of the §3.1 RAM without `njump`
instructions such that for every `n ≥ N₀` and every `A ∈ {0,1}^{n×n}` there is a memory image `D` of at
most `C·n²` bits for which, for all `u, v ∈ {0,1}ⁿ`, the run of `prog` from `D` on the input `u` then
`v` halts with `r₀ = uᵀAv` (`1` if `u_i A_{ij} v_j = 1` for some `i, j`, else `0`) at logarithmic cost
at most `n² / 2^{c·√(log₂ n)}`.

**Formalization Note.** The paper fixes no data-structure model; this is the paper's own §3.1 RAM
(published `Instr`, `Step`, `Reaches`, logarithmic cost), the model in which the proof of Theorem 4
feeds Theorem 15 into Theorem 2. "Deterministically" is the absence of `njump`; the query algorithm is
one program, independent of `n` and `A`, and only the memory image depends on `A` (and `n`). Memory
size is `memBits D`, the total bit length of the preloaded registers. Time is the cost of the run,
halting step included. Preprocessing time is not part of the theorem. -/
theorem theorem_15 :
    ∃ (c C : ℝ) (N₀ : ℕ) (prog : List Instr), 0 < c ∧ NjumpFree prog ∧
      ∀ n : ℕ, N₀ ≤ n → ∀ A : Fin n → Fin n → Bool,
        ∃ D : List ℕ, (memBits D : ℝ) ≤ C * (n : ℝ) ^ 2 ∧
          ∀ u v : Fin n → Bool, ∃ k : ℕ,
            RunsTo prog D (List.ofFn u ++ List.ofFn v)
              (if ∃ i j, u i = true ∧ A i j = true ∧ v j = true then 1 else 0) k ∧
            (k : ℝ) ≤ (n : ℝ) ^ 2 / (2 : ℝ) ^ (c * Real.sqrt (Real.logb 2 n)) := by sorry

end CNFEncComplexity.Supplement
