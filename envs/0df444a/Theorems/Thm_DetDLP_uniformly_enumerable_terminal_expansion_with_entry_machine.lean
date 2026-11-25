-- Prove2me | Theorems.Thm_DetDLP_uniformly_enumerable_terminal_expansion_with_entry_machine
-- name    : DetDLP.uniformly_enumerable_terminal_expansion_with_entry_machine
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T13:51:39.790837+00:00
-- url     : https://prove2.me/theorems/36a7a3ff-a4d5-4bda-a18e-116602e5c4e7
-- title:
--   Uniform enumeration and entry evaluation for one terminal expansion
-- statement:
--   Assume the degree-sensitive scalar contraction machine on encoded scalar networks. For fixed ambient bounds and a fixed original entry evaluator, there exist two fixed multitape machines and a common cutoff. On every sufficiently large valid terminal instance the same residual expansion has a binary defining polynomial, can be enumerated by the first machine, and has its tensor entries evaluated on demand by the second. The enumeration bounds include the number of branches, their digit counts, guard and descriptor sizes and scalar-query dimensions. Both machines run in polynomial space and in polynomial time times two to the power O(b/m) per query.
-- source:
--   Intermediate construction for Theorem 4.3, Sections 5.3–5.4 and Appendix D, S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem.

import Definitions.Def_DetDLP_D4Plan
open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open DetDLP.D4Plan

theorem DetDLP.uniformly_enumerable_terminal_expansion_with_entry_machine
    (hscalar :
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
                (polyBound K (β + desc.length))) (C c : ℕ) (hC : 0 < C) (hc : 0 < c)
    (E : PrimitiveMachine) (o : Fin E.tapeCount) :
    ∃ (A B : PrimitiveMachine) (oa : Fin A.tapeCount) (ob : Fin B.tapeCount)
      (enumCost entryCost L₀ : ℕ), ∀ x : Input C c,
      L₀ ≤ Nat.clog 2 x.S → entry x E o → ∃ P : Plan x,
      (∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1) ∧
      Enumerates A oa enumCost P ∧ Sources B ob entryCost P := by sorry
