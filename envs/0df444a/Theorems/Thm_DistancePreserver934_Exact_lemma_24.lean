-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_24
-- name    : DistancePreserver934.Exact.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:39:06.111241+00:00
-- url     : https://prove2.me/theorems/c0073b67-a16d-425f-af0f-4893fd2c6321
-- title:
--   Lemma 24 — admissible radius and the loss of one Step 2 batch
-- statement:
--   The setting is that of the inductive step of §6: $P$ is a demand set of $G$ with $n^{7/10}<p\le n$, $H$ is a minimal distance preserver of $(G,P)$ with $|E_H|=nd>C\,n^{8/9}p^{4/9}$, and $d,l,r$ are the fixed parameters of Equations (33)–(34). Runs follow the rules of §6.3 (definition `Removal`), with every legal choice of the removed demand, of the batch $(Q,S)$ and of the minimal pruned subgraph.
--
--   For every choice of the Lemma 10 constants $c_0,c_1,c_2$ there is an absolute constant $C_2>0$, independent of $C$, such that for all sufficiently large $C$:
--
--   1. the parameters of Equation (34) satisfy $6\le r\le\min\{d^2,l\}$;
--   2. in every run, each execution of Step 2, removing its batch $Q=R_i\setminus R_{i+1}$ and updating the graph, deletes at most
--   $$C_2\left(n+|Q|\sqrt{\frac{nr}{d}}\right)\tag{37}$$
--   edges.
--
--   Since §6 is a proof by contradiction, once Equation (26) is proved the setting is empty for every admissible $C$; the statement is the source's intermediate step inside that contradiction.
--
--   Differences from the source:
--   - generalization: the run of the procedure, executed until |R| ≤ p/2 → every finite, possibly unfinished, run; reason: the loss totals of a finished run are those of one of these runs
--   - generalization: c₀ > 0, c₁, c₂ the particular constants of Lemma 10 → arbitrary real c₀, c₁, c₂ (C₂ may depend on c₁, c₂); reason: the proof uses only the certificate (36); Lemma 10's constants are a special case
--   - encoding: O(·)/Ω(·) bound with an unspecified absolute constant → one explicit constant, quantified (∃) before every vertex type, graph, demand set and parameter; reason: this is the meaning of the source's absolute-constant O-notation; no instance changes
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 24, printed p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_LoyalCore
import Definitions.Def_DistancePreserver934_Exact_Removal

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 24, printed p.24 / PDF p.25.  For every choice of the Lemma 10 constants there is an
absolute `C₂ > 0` (independent of `C`) such that for all sufficiently large `C`: in the setting
of the inductive step of §6, the parameters of Equation (34) satisfy `6 ≤ r ≤ min{d², l}`, and
each execution of Step 2 (removing its batch `Q` and updating the graph) deletes at most
`C₂ (n + |Q| √(n r / d))` edges (Equation (37)). -/
theorem lemma_24 : ∀ c₀ c₁ c₂ : ℝ, ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      Sec6Setting C G H P →
      Eq5 (sec6d H) (sec6l H P) (sec6r H) ∧
      ∀ (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind),
        IsRun c₀ c₁ c₂ G H P τ st kind → ∀ i < τ, kind i = StepKind.two →
          stepLoss st i ≤ C₂ * (sec6n V + (((st i).2 \ (st (i + 1)).2).card : ℝ) *
            Real.sqrt (sec6n V * sec6r H / sec6d H)) := by sorry

end DistancePreserver934.Exact
