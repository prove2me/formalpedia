-- Prove2me | Theorems.Thm_DetDLP_d4_partial_unroll_rank_enumerator
-- name    : DetDLP.d4_partial_unroll_rank_enumerator
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T05:56:11.563321+00:00
-- url     : https://prove2.me/theorems/c9b73338-f1f5-4f56-9475-4bc933f33163
-- title:
--   Counted partial unrolling of a terminal core
-- statement:
--   Partial unrolling to depth $\lceil\log_{32}(4m)\rceil$ yields a ranked family of weighted residual networks. Rank zero gives the header; each positive rank returns its branch. The branch count, geometry and guarded readout satisfy the plan contract. Given closed continuation, one machine computes the source entries named in those same records.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_partial_unroll_rank_enumerator (one : AppendixD4.OneStep) (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K L₀ : ℕ) (P : (x : Input C c) → L₀ ≤ Nat.clog 2 x.S → entry x E o → Plan x),
      (∀ x hl he, Enumerates A oa K (P x hl he)) ∧
      (AppendixD4.Closed → ∃ (B : PrimitiveMachine) (ob : Fin B.tapeCount) (k : ℕ), ∀ x hl he, Sources B ob k (P x hl he)) := by sorry
