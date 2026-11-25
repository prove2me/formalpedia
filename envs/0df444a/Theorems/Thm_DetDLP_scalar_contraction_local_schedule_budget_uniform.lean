-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_schedule_budget_uniform
-- name    : DetDLP.scalar_contraction_local_schedule_budget_uniform
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-24T20:22:02.804806+00:00
-- url     : https://prove2.me/theorems/de9add25-8179-4f6d-8fb8-1db219c0c7f5
-- title:
--   Uniform schedule budget for scalar contraction (∃K after schedule)
-- statement:
--   Corrected uniform budget comparison for the scalar-contraction local instruction machine: after the schedule outputs (including prepSteps) are fixed, there exists a polynomial degree $K$ bounding the prep+stepper runtime and stack space against the Cauchy–Hermite-style Stage I time formula.
-- source:
--   Liu–Zhang–Ren Formal Paper / DetDLP scalar contraction

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Uniform-in-$\\beta$ budget matching the $\\forall L,\\exists K,\\forall\\beta$ packaging of
`scalar_contraction_local_instructions` (after schedule outputs $B,\\ldots,\\texttt{prepSteps}$). -/
theorem scalar_contraction_local_schedule_budget_uniform
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov)
    (L : ℕ) :
    ∃ K : ℕ,
      ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
        (B T U x y calls depth cap0 prepSteps : ℕ)
        (hβ : 2 ≤ β) (ht : 1 ≤ Told) (he : G.nE ≤ C * β) (hv : G.nV ≤ β ^ c0)
        (hP₁ : 1 ≤ P) (hP₂ : P ≤ C * β) (hl₁ : 1 ≤ ℓ') (hl₂ : ℓ' ≤ C * β)
        (ha : ∀ v t i, A v t i < 2 ^ P)
        (hB : 0 < B),
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
