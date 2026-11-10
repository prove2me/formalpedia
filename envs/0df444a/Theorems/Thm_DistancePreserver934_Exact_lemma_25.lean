-- Prove2me | Theorems.Thm_DistancePreserver934_Exact_lemma_25
-- name    : DistancePreserver934.Exact.lemma_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:39:01.627085+00:00
-- url     : https://prove2.me/theorems/db71114b-7e5e-438a-a00d-b3afa5a272b8
-- title:
--   Lemma 25 (total loss in Step 2)
-- statement:
--   The setting is that of the inductive step of §6: $P$ is a demand set of $G$ with $n^{7/10}<p\le n$, $H$ is a minimal distance preserver of $(G,P)$ with $|E_H|=nd>C\,n^{8/9}p^{4/9}$, and $d,l,r$ are the fixed parameters of Equations (33)–(34). Runs follow the rules of §6.3 (definition `Removal`), with every legal choice of the removed demand, of the batch $(Q,S)$ and of the minimal pruned subgraph.
--
--   For every choice of the Lemma 10 constants with $c_0>0$, for all sufficiently large $C$, along every run the total number of edges removed in Step 2 is at most
--   $$\frac{nd}{20}.$$
--   This includes runs with no Step 2 batch.
--
--   Since §6 is a proof by contradiction, once Equation (26) is proved the setting is empty for every admissible $C$; the statement is the source's intermediate step inside that contradiction.
--
--   Differences from the source:
--   - generalization: the run of the procedure, executed until |R| ≤ p/2 → every finite, possibly unfinished, run; reason: the loss totals of a finished run are those of one of these runs
--   - generalization: c₀ > 0, c₁, c₂ the particular constants of Lemma 10 → arbitrary real c₀ > 0, c₁, c₂ (the threshold for C may depend on them); reason: the proof uses only the certificate (36); Lemma 10's constants are a special case
-- source:
--   Yanyu Chen, Yu Chen, Zihan Tan, Mingyang Yang, Improved Bounds on Distance Preservers, STOC 2027 submission #934 (October 2026), SHA-256 79b3d23a6e7b7fc6148c7a627181474a0129fb2f4c1d04ccd94c1da7987ed76b, Lemma 25 (with Equations (38)–(40) and §6.4), printed p. 24 (PDF p. 25)

import Mathlib
import Definitions.Def_DistancePreserver934_Exact_Preservers
import Definitions.Def_DistancePreserver934_Exact_Essential
import Definitions.Def_DistancePreserver934_Exact_Removal

namespace DistancePreserver934.Exact

open Classical

/-- Lemma 25 (total loss in Step 2), printed p.24 / PDF p.25.  For every choice of the Lemma 10
constants with `c₀ > 0` and all sufficiently large `C`: in the setting of the inductive step of
§6, along every execution of the demand-removal procedure the total number of edges removed in
Step 2 is at most `nd/20`. -/
theorem lemma_25 : ∀ c₀ c₁ c₂ : ℝ, 0 < c₀ → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      Sec6Setting C G H P →
      ∀ (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind),
        IsRun c₀ c₁ c₂ G H P τ st kind →
          kindLoss τ st kind StepKind.two ≤ sec6n V * sec6d H / 20 := by sorry

end DistancePreserver934.Exact
