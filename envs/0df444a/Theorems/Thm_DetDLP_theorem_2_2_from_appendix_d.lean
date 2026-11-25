-- Prove2me | Theorems.Thm_DetDLP_theorem_2_2_from_appendix_d
-- name    : DetDLP.theorem_2_2_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T04:58:34.833959+00:00
-- url     : https://prove2.me/theorems/49fc51fd-d432-4309-b143-933d1124136e
-- title:
--   Bounded-degree tensor network contraction under Appendix D.4
-- statement:
--   Assume the two interfaces of Appendix D.4. Consider a bipartite tensor network at scale $s\ge2$, with at most $Cs$ edges and $s^{c_0}$ vertices, maximum degree at most $\lceil s^{9/10}\rceil$, and precision and truncation length between $1$ and $Cs$. Write $n$ for $s$ plus the descriptor length. Suppose a fixed machine evaluates tensor entries in time $n^{c_0}2^{A s^{9/10}}$ and space $n^{c_0}$. There is a machine independent of the instance that returns the canonical encoding of the contraction in polynomial space and time
--   $$n^{O(1)}2^{O(s/\sqrt{\log s})}.$$
--   The contraction bound applies to networks specified by their entry evaluator; it does not require explicit tables of tensor entries.
-- source:
--   Liu, Zhang, Ren (2026), Theorem 2.2; conditional on OpenAI (Oct 25, 2026), The Exponential Time Hypothesis is False, Appendix D, Section D.4, pp. 57–64.

import Mathlib
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem theorem_2_2_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    ∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s →
            G.nE ≤ C * s →
            G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s →
            1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length)) := by sorry

end DetDLP
