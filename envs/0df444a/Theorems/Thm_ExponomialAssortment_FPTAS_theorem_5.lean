-- Prove2me | Theorems.Thm_ExponomialAssortment_FPTAS_theorem_5
-- name    : ExponomialAssortment.FPTAS.theorem_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T21:15:40.897234+00:00
-- url     : https://prove2.me/theorems/f04f268b-ad23-49de-b454-90d077d9b053
-- title:
--   Theorem 5 — Polynomial-time evaluation and attaining assortment
-- statement:
--   There is a uniform bound of order n⁶η⁻²log²(np_max/p_min) on reachable profitable states. A single binary machine computes an exact objective expression and an attaining feasible assortment for every guessed initial state in time polynomial in n, 1/η and log(p_max/p_min), with constants and degree independent of inputs. The bound is retained literally, with no hidden dependence on utility magnitude or input length.
--
--   Differences from the source:
--   - encoding: one-based indicators and normalized utilities → Fin n, finite selected sets, Valid and Feasible with 1 ≤ C ≤ n; reason: equivalent indexing and the cardinality extension explicitly asserted in §8, counting the outside option; C=n recovers the unconstrained setting
--   - encoding: p_min is the minimum nonzero price → an explicit positive-price witness; reason: this is the nontrivial branch where the source grid and logarithmic ratio are defined; all-zero data remain covered by the headline theorem
--   - encoding: polynomial-time computation of the objective and an attaining assortment → a uniform finite-alphabet machine, binary rational input and exact expression output; reason: §2.4 requires bit complexity; expression syntax represents the exact value without granting free comparisons
--   - encoding: a big-O profitable-state count immediately preceding Theorem 5 → a positive uniform constant and a finite-set cardinality bound in the same item; reason: the item contains both the displayed supporting count and the computational theorem
-- source:
--   Aouad, Feldman and Segev (2023), DOI 10.1287/mnsc.2022.4492, published repository manuscript, Theorem 5, printed p. 19, PDF p. 20

import Definitions.Def_ExponomialAssortment_FPTAS_Computation

namespace ExponomialAssortment.FPTAS

theorem theorem_5 :
    (∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (I : Instance n), Valid I →
      ∀ C, 2 ≤ C → C ≤ n → ∀ η : ℝ, 0 < η → (∃ i, 0 < I.price i) →
      ∀ l f, bestSingle I η l → f ≠ I.outside →
      Set.Finite {s | Reachable I C η l f s ∧ Profitable I η l s} ∧
      (Nat.card {s // Reachable I C η l f s ∧ Profitable I η l s} : ℝ) ≤
        K * n^6 / η^2 * (Real.log (n * pmax I / pmin I))^2) ∧
    ∃ (M : BinaryMachine) (c d : ℕ), 0 < c ∧
      ∀ q : RationalInput, NormalInput q → 2 ≤ q.capacity →
      (∃ i, 0 < q.price i) → ∀ f : Fin q.n, f ≠ q.outside →
      ∃ (S : Finset (Fin q.n)) (a : ExactExpr) (t : ℕ) (l : Fin q.n),
        MachineRuns M (encodeInput q ++ encodeNat f.val)
          (encodeSet S ++ encodeExpr a) t ∧ t ≤ EvaluationBound c d q ∧
        bestSingle q.model q.accuracy l ∧
        PrunedOptimal q.model q.capacity q.accuracy l f S a.eval := by sorry

end ExponomialAssortment.FPTAS
