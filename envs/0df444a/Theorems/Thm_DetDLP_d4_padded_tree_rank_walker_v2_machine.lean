-- Prove2me | Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine
-- name    : DetDLP.d4_padded_tree_rank_walker_v2_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T10:30:52.636175+00:00
-- url     : https://prove2.me/theorems/86f79f96-713f-4612-867a-c22d9e3c5cfb
-- title:
--   Padded rank-tree walker with a single final weight shift
-- statement:
--   At every active depth the walker sends exactly the specified node query. Given a machine for answering the queries on a rank transcript, a single machine reads the padded tree at that rank, with at most three times the node budget in loop rounds. Its time is polynomial in transcript word length and node budget times the oracle time plus one, and its space is polynomial in the same parameters plus a constant multiple of the oracle space plus one.

import Definitions.Def_DetDLP_D4WalkerTranscriptV2
set_option autoImplicit false
open DetDLP DetDLP.D4RankWalker DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_padded_tree_rank_walker_v2_machine (O : PrimitiveMachine) (o : Fin O.tapeCount) :
    (∀ (S m p guard l : ℕ) (f : Polynomial ℤ) (i : WorkItem) (j : ℕ), i.depth < Nat.clog 32 (4*m) →
      ask (contextV2 S m p guard l (AppendixD4.polynomialBits f)) i.bits j =
      D4NodeQuery.request i.G (fun v : Fin i.pins.length => (i.pins.get v).2)
        (D3Stopped.shift S i.depth) (D3Stopped.width S i.depth) i.pCurr l f j) ∧
    ∃ (A : PrimitiveMachine) (oa : Fin A.tapeCount) (K : ℕ),
      ∀ (S m p guard l : ℕ) (f : Polynomial ℤ) (root : WorkItem) (F : Wd → WalkerStep) (B u : ℕ) (τ σ : ℝ),
        let ctx := contextV2 S m p guard l (AppendixD4.polynomialBits f)
        let cs := runCallsV2 ctx root F B u
        let input := startV2 ctx root B u
        let output := tag ((unrollRankTreeV2 ctx root F).read B u)
        let N := 64^(Nat.clog 32 (4*m)); let L := maxLen input output cs
        0 ≤ τ → 0 ≤ σ → (∀ e ∈ cs, RunsWithin O o e.2.1 e.2.2 τ σ) →
        cs.length+1 ≤ 3*N ∧ RunsWithin A oa input output (polyBound K (L+N)*(τ+1)) (polyBound K (L+N)+K*(σ+1)) := by sorry
