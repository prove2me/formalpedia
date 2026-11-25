-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_instructions_v2_to_v1
-- name    : DetDLP.scalar_contraction_local_instructions_v2_to_v1
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T00:56:49.626972+00:00
-- url     : https://prove2.me/theorems/3e18a47f-41d7-42e6-8dfd-7793113fa43d
-- title:
--   Quantifier bridge from instructions v2 to v1
-- statement:
--   If the pointwise packaging of instructions_v2 holds, then the uniform-in-beta packaging of instructions v1 holds for the same machines.
-- source:
--   DetDLP

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Quantifier bridge: pointwise `∃ K` packaging (v2) yields uniform-in-`β` packaging (v1). -/
theorem scalar_contraction_local_instructions_v2_to_v1
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    (∃ (s lp lc : ℕ) (prep : BitProgram.Program 8 (20 + s) lp) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ (L : ℕ) (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
        2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
        1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
        (∀ v t i, A v t i < 2 ^ P) →
        (∀ v t (regs : Fin 3 → Bool),
          let q := (encodePortQuery desc v.val (List.ofFn t)).tail
          let start : BitProgram.Cfg 3 se le := ⟨some Q.entry, regs, fun j =>
            if j = it then List.replicate q.length true else if j = iv then q else []⟩
          ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n ≤ 8 * Told ∧ BitProgram.Trace Q n start c ∧
            c.pc = none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd) =
              encodeNatListBin (List.ofFn (A v t)) ∧
            ∀ j b, j ≤ n → BitProgram.Trace Q j start b → ∀ i, (b.stacks i).length ≤ (β + desc.length) ^ c0 + 8) →
        let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
        let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
        let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
          Polynomial.monomial i.val (A v t i : ℤ))
        let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
          ((Z.coeff i.val : ZMod (2 ^ P)).val))
        let word := w.foldr (fun b z => b.toNat + 2 * z) 1
        ∃ (context : Fin s → List Bool) (F : ℕ → ℕ → Answer) (B T U x y calls depth cap0 prepSteps : ℕ)
          (reg : Fin 8 → Bool),
          0 < B ∧ (∀ i, (context i).length ≤ U) ∧
            Computes F B x y word calls depth ∧ reg 1 = true ∧
            ∃ K : ℕ,
              let q := B + 1
              let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
                let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
                Fin.addCases (m := 20) (n := s) (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
              let small (z : Answer) := match z with
                | .value v => v < B
                | .call a b => a < B ∧ b < B
              let returned (a b stack : ℕ) (z : Answer) := match z with
                | .value v => pack a b stack 0 v 0
                | .call save child => pack a b stack 1 child save
              (∀ (a b stack : ℕ) (r : Fin 8 → Bool), a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
                let start : BitProgram.Cfg 8 (20 + s) lc := ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
                ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
                  BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
                  ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c → ∀ i, (c.stacks i).length ≤ U) ∧
              let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
              let overhead := L * (q.size * (depth + 1) + 3) ^ 2
              BitProgram.Trace prep prepSteps start ⟨none, reg, pack x y 1 0 0 0⟩ ∧
              (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c → ∀ i, (c.stacks i).length ≤ cap0) ∧
              ((prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13) : ℕ) : ℝ) ≤
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) *
                    ((β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
                      ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)))) ∧
              max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K) →
    ∃ (s lp lc : ℕ) (prep : BitProgram.Program 8 (20 + s) lp) (stepper : BitProgram.Program 8 (20 + s) lc),
      ∀ L : ℕ, ∃ K : ℕ,
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
            2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
            (∀ v t i, A v t i < 2 ^ P) →
            (∀ v t (regs : Fin 3 → Bool),
              let q := (encodePortQuery desc v.val (List.ofFn t)).tail
              let start : BitProgram.Cfg 3 se le := ⟨some Q.entry, regs, fun j =>
                if j = it then List.replicate q.length true else if j = iv then q else []⟩
              ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n ≤ 8 * Told ∧
                BitProgram.Trace Q n start c ∧ c.pc = none ∧
                ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd) =
                  encodeNatListBin (List.ofFn (A v t)) ∧
                ∀ j b, j ≤ n → BitProgram.Trace Q j start b → ∀ i, (b.stacks i).length ≤ (β + desc.length) ^ c0 + 8) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
              Polynomial.monomial i.val (A v t i : ℤ))
            let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
              ((Z.coeff i.val : ZMod (2 ^ P)).val))
            let word := w.foldr (fun b z => b.toNat + 2 * z) 1
            ∃ (context : Fin s → List Bool) (F : ℕ → ℕ → Answer) (B T U x y calls depth cap0 prepSteps : ℕ)
              (reg : Fin 8 → Bool), 0 < B ∧ (∀ i, (context i).length ≤ U) ∧
              Computes F B x y word calls depth ∧ reg 1 = true ∧
              let q := B + 1
              let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
                let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
                Fin.addCases (m := 20) (n := s) (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
              let small (z : Answer) := match z with
                | .value v => v < B
                | .call a b => a < B ∧ b < B
              let returned (a b stack : ℕ) (z : Answer) := match z with
                | .value v => pack a b stack 0 v 0
                | .call save child => pack a b stack 1 child save
              (∀ (a b stack : ℕ) (r : Fin 8 → Bool), a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
                let start : BitProgram.Cfg 8 (20 + s) lc := ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
                ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
                  BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
                  ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c → ∀ i, (c.stacks i).length ≤ U) ∧
              let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
              let overhead := L * (q.size * (depth + 1) + 3) ^ 2
              BitProgram.Trace prep prepSteps start ⟨none, reg, pack x y 1 0 0 0⟩ ∧
              (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c → ∀ i, (c.stacks i).length ≤ cap0) ∧
              ((prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13) : ℕ) : ℝ) ≤
                (polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) *
                    ((β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
                      ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)))) ∧
              max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K := by sorry

end DetDLP
