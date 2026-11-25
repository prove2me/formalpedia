-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_uniform_close_v4
-- name    : DetDLP.scalar_contraction_local_uniform_close_v4
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:59:26.047672+00:00
-- url     : https://prove2.me/theorems/4aac137f-7522-51ed-916a-459f7b1f4909
-- title:
--   Uniform budget for one value-return
-- statement:
--   Suppose a preparation program meets the uniform oracle bound, and a stepper meets the linear copy bound. Then those two programs satisfy the uniform-in-$\beta$ packaging of the local scalar-contraction instructions. For each external budget $L$ there is one degree $K$, independent of the instance, such that a single value-return at depth $0$ with $B=\mathrm{word}+1$ obeys both the subexponential time inequality and the polynomial space inequality.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026, Section 5.2. Corrected local-instruction packaging: preparation depends on the port oracle, and the stepper step and stack bounds are existential and linear in the answer length.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- Polynomial extras of a linear stepper fit under one larger uniform degree. -/
theorem scalar_contraction_local_uniform_close_v4
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov)
    (s lp lc : ℕ) (hs : 0 < s)
    (prep : BitProgram.Program 8 (20 + s) lp)
    (stepper : BitProgram.Program 8 (20 + s) lc)
    (hprep :
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
            ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n ≤ 8 * Told ∧ BitProgram.Trace Q n start c ∧
              c.pc = none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd) =
                encodeNatListBin (List.ofFn (A v t)) ∧
              ∀ j b, j ≤ n → BitProgram.Trace Q j start b →
                ∀ i, (b.stacks i).length ≤ (β + desc.length) ^ c0 + 8) →
          let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
          let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
          let expr : ℝ :=
            (β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
              ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)
          let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
            Polynomial.monomial i.val (A v t i : ℤ))
          let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
            ((Z.coeff i.val : ZMod (2 ^ P)).val))
          let word := w.foldr (fun b z => b.toNat + 2 * z) 1
          let context : Fin s → List Bool := fun i => if i.val = 0 then word.bits else []
          let reg : Fin 8 → Bool := fun _ => true
          let qn := word + 2
          let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
            let v : Fin 12 → ℕ := ![qn, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
            Fin.addCases (m := 20) (n := s)
              (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
          let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
          ∃ (prepSteps cap0 U : ℕ),
            (∀ i, (context i).length ≤ U) ∧
            BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
            (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
              ∀ i, (c.stacks i).length ≤ cap0) ∧
            ((prepSteps : ℕ) : ℝ) ≤
              polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) ∧
            cap0 ≤ K * (β + desc.length + 1) ^ K )
    (hstep :
      ∀ (answer B depth : ℕ) (context : Fin s → List Bool),
        0 < B → answer < B → context ⟨0, hs⟩ = answer.bits →
        let M := (List.ofFn (fun i => (context i).length)).foldl Nat.max 0
        let F : ℕ → ℕ → Answer := fun _ _ => .value answer
        let q := B + 1
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let small (z : Answer) := match z with
          | .value v => v < B
          | .call a b => a < B ∧ b < B
        let returned (a b stack : ℕ) (z : Answer) := match z with
          | .value v => pack a b stack 0 v 0
          | .call save child => pack a b stack 1 child save
        ∃ (T U : ℕ),
          (∀ i, (context i).length ≤ U) ∧
          T ≤ 100 * (answer.bits.length + 1) ∧
          U ≤ M + ((q ^ (depth + 1)).bits.length) + 4 ∧
          ∀ (a b stack : ℕ) (r : Fin 8 → Bool),
            a < B → b < B → stack < q ^ (depth + 1) → small (F a b) →
            let start : BitProgram.Cfg 8 (20 + s) lc :=
              ⟨some stepper.entry, r, pack a b stack 0 0 0⟩
            ∃ (steps : ℕ) (r' : Fin 8 → Bool), steps ≤ T ∧
              BitProgram.Trace stepper steps start ⟨none, r', returned a b stack (F a b)⟩ ∧
              ∀ j c, j ≤ steps → BitProgram.Trace stepper j start c →
                ∀ i, (c.stacks i).length ≤ U ) :
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
              max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K  := by sorry

end DetDLP
