-- Prove2me | Theorems.Thm_DetDLP_integer_coefficient_contraction_schedule
-- name    : DetDLP.integer_coefficient_contraction_schedule
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:13:04.449933+00:00
-- url     : https://prove2.me/theorems/e0203304-d374-4dc3-8892-6ccac0d42f23
-- title:
--   Integer coefficients of a scalar network under the recursive depth schedule
-- statement:
--   A uniform machine receives a bipartite network whose local evaluator supplies bounded nonnegative integer coefficient vectors. It outputs the low coefficients of the ordinary integer-polynomial contraction reduced to canonical binary residues modulo 2 to the precision P. Its time bound charges the entry oracle, the direct leaf cost and the sum of the per-depth exponents at scales beta/8^d and rho/2^d; space is polynomial. This intermediate algorithmic claim isolates construction and analysis of the scalar contraction machine.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Section 5.2, proof of Lemma 5.2 (intermediate machine specification).

import Mathlib
import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem integer_coefficient_contraction_schedule :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            (∀ v t i, A v t i < 2^P) →
            (∀ v t, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn t))
              (encodeNatListBin (List.ofFn (A v t))) (Told : ℝ) (((β+desc.length : ℕ) : ℝ)^c0)) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
              Polynomial.monomial i.val (A v t i : ℤ))
            let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
              ((Z.coeff i.val : ZMod (2^P)).val))
            RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
              (polyBound K (β+desc.length) * (Told : ℝ) * (2 : ℝ)^((K : ℝ) *
                ((β : ℝ)/Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ+1),
                 ((β : ℝ)/(8 : ℝ)^d) / Real.sqrt ((ρ : ℝ)/(2 : ℝ)^d))))
              (polyBound K (β+desc.length)) := by sorry

end DetDLP
