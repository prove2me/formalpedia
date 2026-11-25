-- Prove2me | Theorems.Thm_DetDLP_d4_outer_scalar_cursor_machine
-- name    : DetDLP.d4_outer_scalar_cursor_machine
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T05:55:59.291097+00:00
-- url     : https://prove2.me/theorems/d94be272-947f-4151-b8e8-a7615fc315c0
-- title:
--   Streaming scalar accumulation and guarded word readout
-- statement:
--   Given a small-regime routine, a rank enumerator and a uniform digit-entry evaluator, a single machine contracts all terminal instances. On large instances it enumerates each residual rank and digit assignment, contracts the scalar query, and accumulates the weighted unpacked result. The output is the canonical coefficient word in the stated terminal time and polynomial space.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4_outer_scalar_cursor_machine (hscalar :
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
                (polyBound K (β + desc.length)))
    (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) (L₀ e s d : ℕ)
    (A F D : PrimitiveMachine) (oa : Fin A.tapeCount) (of₀ : Fin F.tapeCount) (od : Fin D.tapeCount)
    (small : ∀ x : Input C c, Nat.clog 2 x.S < L₀ → entry x E o → RunsWithin F of₀ (input x) (answer x) (polyBound s (size x)) (polyBound s (size x)))
    (large : ∀ x : Input C c, L₀ ≤ Nat.clog 2 x.S → entry x E o → ∃ P : Plan x, Enumerates A oa e P ∧ Digits D od d P) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (K : ℕ), ∀ x : Input C c, entry x E o → RunsWithin M om (input x) (answer x) (time x K) (polyBound K (size x)) := by sorry
