-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_3_minkt
-- name    : ContractionLemma.Supplement.theorem_3_minkt
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:22:33.87222+00:00
-- url     : https://prove2.me/theorems/a94233e4-6965-4bf8-ab90-3bb32e61585c
-- title:
--   Theorem 3, p.25 — MINKT, the number of programs, $K^T_U(x)$ and a shortest program in time $2^{O(N/\sqrt{\log N})}$
-- statement:
--   Let $U$ be a fixed deterministic local machine with an output tape. A program for $x$ is a binary string $p$ such that $U$, started with $p$ on its input tape, halts within $T$ steps with exactly $x$ on its output tape; $K^T_U(x)$ is the length of a shortest program for $x$. On the instance $(x,1^T,1^s)$, $N=|x|+T+s$, each of the following can be computed in time $2^{O(N/\sqrt{\log N})}$ and polynomial space:
--
--   1. whether $(x,1^T,1^s)\in\mathsf{MINKT}_U$, i.e. some program of length at most $s$ prints $x$ within $T$ steps;
--   2. the number of programs of length at most $s$ for $x$;
--   3. $K^T_U(x)$, or the report that $x$ has no program;
--   4. a shortest program for $x$, or the report that there is none.
--
--   The bounds are $C\,2^{C N/\sqrt{\log_2(N+2)}}$ in time and $C(N+1)^C$ in space, $C$ depending only on $U$. This places a meta-complexity problem in subexponential time without any hardness assumption.
--
--   Differences from the source:
--   - generalization: a fixed universal local machine $U$ → every fixed deterministic local machine $U$ with an output tape; reason: the proof never uses universality; a universal $U$ is a special case
--   - encoding: $K^T_U(x)$, which may be infinite → an optional number, "none" when $x$ has no program; likewise for the shortest program; reason: the proof reports that no program exists
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 3, p.25 (stated first on p.5); §4.1, p.25

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Classes

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped Classical
/-- **Theorem 3 (MINKT)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256
049caea1…), p.25 (PDF p.28; stated first on p.5).

"`MINKT_U` can be decided in time `2^{O(N/√log N)}`, where `N = |x| + T + s` is the length of the
instance. Within the same bound one can count the programs of length at most `s` that make `U` print
`x` within `T` steps, compute `K^T_U(x)`, and find a shortest program."

For every fixed deterministic local machine `U` there are machines and a constant `C` such that on
the instance `(x, 1^T, 1^s)`, `N = |x| + T + s`, each runs in time `C 2^{C f(N)}`
(`f(N) = N/√log₂(N+2)`) and space `C (N+1)^C` and outputs, respectively: whether some program of
length at most `s` prints `x` within `T` steps; the number of such programs; `K^T_U(x)`, or `none`
if `x` has no program; and a shortest program, or `none`.

**Formalization Note.** The paper fixes a universal local machine `U` but its proof never uses
universality, so the theorem is stated for every fixed deterministic local machine `U` with an output
tape (a generalization). A program is a binary string on `U`'s input tape. The polynomial-space
clause is the paper's convention (p.3). -/
theorem theorem_3_minkt (p : LocalParams) (U : LProgram p) (hU : U.IsDet) :
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (x : List Bool) (T s : ℕ),
      ContractionLemma.RunsWithin A out (minktInput x T s) [decide (MINKT U (minktInput x T s))]
        (C * (2 : ℝ) ^ (C * fScale ((x.length + T + s : ℕ) : ℝ)))
        (C * (((x.length + T + s : ℕ) : ℝ) + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (x : List Bool) (T s : ℕ),
      ContractionLemma.RunsWithin A out (minktInput x T s) (countWord (programCount U x T s))
        (C * (2 : ℝ) ^ (C * fScale ((x.length + T + s : ℕ) : ℝ)))
        (C * (((x.length + T + s : ℕ) : ℝ) + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (x : List Bool) (T s : ℕ),
      ∃ o : Option ℕ, IsKT U x T o ∧
        ContractionLemma.RunsWithin A out (minktInput x T s) (optWord (o.map countWord))
          (C * (2 : ℝ) ^ (C * fScale ((x.length + T + s : ℕ) : ℝ)))
          (C * (((x.length + T + s : ℕ) : ℝ) + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ (x : List Bool) (T s : ℕ),
      ∃ o : Option (List Bool), IsShortestProgram U x T o ∧
        ContractionLemma.RunsWithin A out (minktInput x T s) (optWord (o.map bitsWord))
          (C * (2 : ℝ) ^ (C * fScale ((x.length + T + s : ℕ) : ℝ)))
          (C * (((x.length + T + s : ℕ) : ℝ) + 1) ^ C)) := by sorry

end ContractionLemma.Supplement
