-- Prove2me | Theorems.Thm_DetDLP_lemma_5_2_from_appendix_d
-- name    : DetDLP.lemma_5_2_from_appendix_d
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T04:57:57.053857+00:00
-- url     : https://prove2.me/theorems/2b837399-603c-460f-b360-bc7e9c9dea71
-- title:
--   Degree-sensitive contraction under Appendix D.4
-- statement:
--   Assume the two interfaces of Appendix D.4. Let a bipartite tensor network at scale $\beta\ge2$ have at most $C\beta$ edges and $\beta^{c_0}$ vertices, with precision and truncation length between $1$ and $C\beta$. Suppose a fixed evaluator returns each tensor entry in time $T_{\rm old}\ge1$ and space $n^{c_0}$, where $n$ is the scale plus the descriptor length. Put $\bar\Delta=\max\{\Delta(G),\lceil\beta^{9/10}\rceil\}$ and $\rho=\max\{1,\lfloor\log_2(\beta/\bar\Delta)\rfloor\}$. One machine, fixed independently of the network, returns the encoded contraction in polynomial space and time
--   $$n^{O(1)}T_{\rm old}\,2^{O(\beta/\sqrt{\rho})}.$$
--   The parameter $\rho$ makes the dependence on the maximum vertex degree explicit.
-- source:
--   Liu, Zhang, Ren (2026), Lemma 5.2; conditional on OpenAI (Oct 25, 2026), The Exponential Time Hypothesis is False, Appendix D, Section D.4, pp. 57–64.

import Mathlib
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem lemma_5_2_from_appendix_d (hOAI : OpenAIAppendixDPremise) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length)) := by sorry

end DetDLP
