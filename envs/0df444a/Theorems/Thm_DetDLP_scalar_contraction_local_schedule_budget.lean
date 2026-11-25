-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_schedule_budget
-- name    : DetDLP.scalar_contraction_local_schedule_budget
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T19:15:32.373091+00:00
-- url     : https://prove2.me/theorems/2669c487-b4a1-4bfa-b107-14b5433647d0
-- title:
--   Degree-sensitive schedule budget after prepSteps witness
-- statement:
--   Corrects scalar_contraction_local_node_budget: existential budget constant K is quantified after adaptive schedule outputs (prepSteps), not before an unbounded prepSteps universal.
-- source:
--   DetDLP Lemma 5.2 / Theorem 3.1, private mission correction

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Correction of `scalar_contraction_local_node_budget`: `∃ K` after schedule outputs. -/
theorem scalar_contraction_local_schedule_budget
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov)
    (L : ℕ)
    (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
    (B T U x y calls depth cap0 prepSteps : ℕ)
    (hβ : 2 ≤ β) (ht : 1 ≤ Told) (he : G.nE ≤ C * β) (hv : G.nV ≤ β ^ c0)
    (hP₁ : 1 ≤ P) (hP₂ : P ≤ C * β) (hl₁ : 1 ≤ ℓ') (hl₂ : ℓ' ≤ C * β)
    (ha : ∀ v t i, A v t i < 2 ^ P)
    (hB : 0 < B) :
    ∃ K : ℕ,
      let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
      let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
      let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
        Polynomial.monomial i.val (A v t i : ℤ))
      let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
        ((Z.coeff i.val : ZMod (2 ^ P)).val))
      let q := B + 1
      let overhead := L * (q.size * (depth + 1) + 3) ^ 2
      ((prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13) : ℕ) : ℝ) ≤
        (polyBound K (β + desc.length) * (Told : ℝ) *
          (2 : ℝ) ^ ((K : ℝ) *
            ((β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
              ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)))) ∧
      max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K := by sorry
end DetDLP
