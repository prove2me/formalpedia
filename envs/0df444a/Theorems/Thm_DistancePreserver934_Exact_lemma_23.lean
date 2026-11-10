-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_23
-- name    : DistancePreserver934.Exact.lemma_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:45.257577+00:00
-- url     : https://prove2.me/theorems/035bffd6-2223-4868-8aa9-aa7b5c3f93bc
-- title:
--   Lemma 23 (total loss in Step 1)
-- statement:
--   The setting is that of the inductive step of §6: $P$ is a demand set of $G$ with $n^{7/10}<p\le n$, $H$ is a minimal distance preserver of $(G,P)$ with $|E_H|=nd>C\,n^{8/9}p^{4/9}$, and $d,l,r$ are the fixed parameters of Equations (33)–(34). Runs follow the rules of §6.3 (definition `Removal`), with every legal choice of the removed demand, of the batch $(Q,S)$ and of the minimal pruned subgraph.
--
--   Along every run, the total number of edges removed in Step 1 is at most
--   $$\frac{nd}{5}.$$
--   This holds for every constant $C$ and every choice of the Lemma 10 constants used by Step 2, including runs without Step 1 removals.
--
--   Since §6 is a proof by contradiction, once Equation (26) is proved the setting is empty for every admissible $C$; the statement is the source's intermediate step inside that contradiction.
--
--   Differences from the source:
--   - generalization: the run of the procedure, executed until |R| ≤ p/2 → every finite, possibly unfinished, run; reason: the loss totals of a finished run are those of one of these runs
--   - generalization: C the fixed (large) induction constant and c₀, c₁, c₂ the constants of Lemma 10 → arbitrary real C, c₀, c₁, c₂; reason: the bound uses only the Step 1 rule and pl = nd/5; the source's constants are a special case
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 23, printed p. 23 (PDF p. 24)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_Removal

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 23 (total loss in Step 1), printed p.23 / PDF p.24.  In the setting of the inductive
step of §6 (any constant `C`), along every execution of the demand-removal procedure (with any
Lemma 10 constants `c₀, c₁, c₂`), the total number of edges removed in Step 1 is at most `nd/5`. -/
theorem lemma_23 {V : Type} [Fintype V] (c₀ c₁ c₂ C : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (hset : Sec6Setting C G H P)
    (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    kindLoss τ st kind StepKind.one ≤ sec6n V * sec6d H / 5 := by sorry

end DistancePreserver934.Exact
