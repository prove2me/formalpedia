-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_scalar_uniform
-- name    : DetDLP.d4b_outer_scalar_uniform
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T09:10:19.105531+00:00
-- url     : https://prove2.me/theorems/d916d137-8c28-449f-bed3-ef2de27618b7
-- title:
--   Uniform scalar oracle for supplied digit tensors
-- statement:
--   A single scalar machine evaluates every digit query of every supplied plan. The coefficient replies satisfy the branch reconstruction identity, the precision cap, polynomial space, and terminal running time.
-- source:
--   Resource accounting for outer scalar cursor dc44082d-fc56-402c-8efa-dc7eda4aebd8.

import Definitions.Def_DetDLP_D4BOuterInvariant
set_option autoImplicit false
open DetDLP DetDLP.D4BOuter DetDLP.D4Plan DetDLP.D4BEntry DetDLP.ResidualScalarOracle OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4b_outer_scalar_uniform (hscalar : ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
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
                (polyBound K (β + desc.length))) (C c e d : ℕ) (hc : 0<C) (D : PrimitiveMachine) (od : Fin D.tapeCount) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (j : ℕ), ∀ {x : Input C c} (P : Plan x) {A o}, Enumerates A o e P → Digits D od d P →
      ∃ v : DigitsData P, (∀ u, unpack P.f x.l (qprec P) (P.R u) (h P u) (J P u) (v u) = BTNContract (P.R u) (P.V u)) ∧
      (∀ u a i, v u a i < 2^precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) ∧
      ∀ u a, RunsWithin M om (dgQuery P u a) (dgAns P v u a) (time x j) (polyBound j (size x)) := by sorry
