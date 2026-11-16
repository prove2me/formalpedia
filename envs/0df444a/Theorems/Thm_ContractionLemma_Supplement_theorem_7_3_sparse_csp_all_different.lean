-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_7_3_sparse_csp_all_different
-- name    : ContractionLemma.Supplement.theorem_7_3_sparse_csp_all_different
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:25:57.969196+00:00
-- url     : https://prove2.me/theorems/4de76acb-271d-472b-b780-3fffce8777a4
-- title:
--   Theorem 7.3, p.35 — counting solutions of sparse CSPs with an all-different constraint in time $\mathrm{poly}(L)2^{O(\sqrt n\log n)}E((n+m)\log n)$
-- statement:
--   Consider a constraint satisfaction problem with $n$ variables over the domain $[n]$ and $m$ constraints, each of arity at most a fixed $k$ and given by a predicate computable in polynomial time, together with an all-different constraint on all $n$ variables. Its solutions (the permutations of $[n]$ that satisfy every constraint) can be counted deterministically in time
--
--   $$
--   \mathrm{poly}(L)\;2^{O(\sqrt n\log n)}\;E\bigl((n+m)\log n\bigr)
--   $$
--
--   and polynomial space. In particular, if $m=o(n\sqrt{\log n})$, the time is $\mathrm{poly}(L)\,2^{o(n\log n)}$, below the $2^{\Theta(n\log n)}$ of exhaustive search over permutations.
--
--   The constants depend only on $k$ and on the polynomial-time predicate algorithm.
--
--   Differences from the source:
--   - encoding: "each given by a predicate computable in polynomial time" → predicates computed by one fixed machine $E$ from the instance, the constraint index and the values, in time and space $c(L+1)^c$; reason: the base mission's reading of entry algorithms
--   - reading: "for $m=o(n\sqrt{\log n})$ this is $2^{o(n\log n)}$" → time $C'(L+1)^{C'}2^{g(n)}$ with $g(n)/(n\log_2(n+2))\to0$, for every $m(n)$ with $m(n)/(n\sqrt{\log_2(n+2)})\to0$; reason: "this" is the preceding bound, which carries the factor $\mathrm{poly}(L)$
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 7.3, p.35

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 7.3 (Sparse CSPs with all-different)** — Gajulapalli, *The Contraction Lemma Beyond
ETH* (manuscript, sha256 049caea1…), p.35 (PDF p.38).

"Consider a constraint satisfaction problem as above with `d = n` and an all-different constraint on
all `n` variables. Its solutions can be counted in time `poly(L) 2^{O(√n log n)} E((n + m) log n)`.
In particular, for `m = o(n√log n)` this is `2^{o(n log n)}`."

"As above" (p.35): `n` variables over the domain `[n]`, `m` constraints of constant arity, each given
by a predicate computable in polynomial time. For every arity bound `k`, constant `c` and predicate
machine `E`, there are a machine `A` and a constant `C` such that on every instance whose scopes
have at most `k` variables and whose predicates `E` computes in time and space `c (L+1)^c`, `A`
outputs the number of solutions (permutations of `[n]` satisfying every constraint) in time
`C (L+1)^C 2^{C √n log₂(n+2)} 2^{C f((n+m) log₂(n+2))}` and space `C (L+1)^C`; and for every `m(n)`
with `m(n)/(n√log₂(n+2)) → 0` there are `g` with `g(n)/(n log₂(n+2)) → 0` and `C'` such that `A`
runs in time `C' (L+1)^{C'} 2^{g(n)}` on instances with at most `m(n)` constraints.

**Formalization Note.** The predicates are given by a fixed machine `E` reading the instance, the
constraint index and the values of its scope (the base reading of an entry algorithm). "This is
`2^{o(n log n)}`" keeps the factor `poly(L)` of the bound it refers to. `f(u) = u/√log₂(u+2)`. The
polynomial-space clause is the paper's convention (p.3). -/
theorem theorem_7_3_sparse_csp_all_different :
    ∀ (k c : ℕ) (E : PrimitiveMachine) (outE : Fin E.tapeCount),
    ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
    (∀ (I : CSPInst) (pred : Fin I.m → List (Fin I.n) → Bool),
      (∀ sc ∈ I.scopes, sc.length ≤ k) →
      (∀ (j : Fin I.m) (vals : List (Fin I.n)), vals.length = (I.scopes.get j).length →
        ContractionLemma.RunsWithin E outE (I.predInput j vals) [pred j vals]
          (c * ((I.encode.length : ℝ) + 1) ^ c) (c * ((I.encode.length : ℝ) + 1) ^ c)) →
      ContractionLemma.RunsWithin A out I.encode (countWord (I.count pred))
        (C * ((I.encode.length : ℝ) + 1) ^ C *
          (2 : ℝ) ^ (C * Real.sqrt I.n * Real.logb 2 (I.n + 2)) *
          (2 : ℝ) ^ (C * fScale ((I.n + I.m) * Real.logb 2 (I.n + 2))))
        (C * ((I.encode.length : ℝ) + 1) ^ C)) ∧
    ∀ mf : ℕ → ℕ,
      Filter.Tendsto (fun n : ℕ => (mf n : ℝ) / (n * Real.sqrt (Real.logb 2 (n + 2))))
        Filter.atTop (nhds 0) →
      ∃ (g : ℕ → ℝ) (C' : ℕ),
        Filter.Tendsto (fun n : ℕ => g n / (n * Real.logb 2 (n + 2))) Filter.atTop (nhds 0) ∧
        ∀ (I : CSPInst) (pred : Fin I.m → List (Fin I.n) → Bool),
          (∀ sc ∈ I.scopes, sc.length ≤ k) →
          (∀ (j : Fin I.m) (vals : List (Fin I.n)), vals.length = (I.scopes.get j).length →
            ContractionLemma.RunsWithin E outE (I.predInput j vals) [pred j vals]
              (c * ((I.encode.length : ℝ) + 1) ^ c) (c * ((I.encode.length : ℝ) + 1) ^ c)) →
          I.m ≤ mf I.n →
          RunsInTime A out I.encode (countWord (I.count pred))
            (C' * ((I.encode.length : ℝ) + 1) ^ C' * (2 : ℝ) ^ g I.n) := by sorry

end ContractionLemma.Supplement
