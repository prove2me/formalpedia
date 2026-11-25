-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_stack_driver
-- name    : DetDLP.scalar_contraction_stack_driver
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T15:57:20.985853+00:00
-- url     : https://prove2.me/theorems/f83e923a-2ae7-4231-bcf4-9cacd287470d
-- title:
--   Polynomial-space Boolean-stack driver for scalar tensor contraction
-- statement:
--   Given a finite three-register stack subroutine for local entry queries in the specified presence/value format, construct a finite Boolean-stack program computing the low integer contraction coefficients modulo the requested power of two. The program must handle the framed graph and tensor description, call the supplied evaluator, return the canonical coefficient word and success flag, and satisfy the degree-sensitive running time and polynomial stack bounds at every prefix. The constants and program can depend only on the fixed structural constants and entry subroutine.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.2, executable recursion and resource accounting in the Boolean-stack language.

import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem scalar_contraction_stack_driver
    (C c0 : ℕ) (hC : 0<C) (hc0 : 0<c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it≠iv) (ho : ot≠ov) :
    ∃ (r s l : ℕ) (driver : BitProgram.Program r s l) (out : Fin s) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            (∀ v t i, A v t i < 2^P) →
            (∀ v t (regs : Fin 3→Bool),
              let q := (encodePortQuery desc v.val (List.ofFn t)).tail
              let start : BitProgram.Cfg 3 se le := ⟨some Q.entry,regs,fun j =>
                if j=it then List.replicate q.length true else if j=iv then q else []⟩
              ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n≤8*Told ∧ BitProgram.Trace Q n start c ∧
                c.pc=none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd)=
                  encodeNatListBin (List.ofFn (A v t)) ∧
                ∀ j b,j≤n→ BitProgram.Trace Q j start b→∀ i,(b.stacks i).length≤(β+desc.length)^c0+8) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
              Polynomial.monomial i.val (A v t i : ℤ))
            let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
              ((Z.coeff i.val : ZMod (2^P)).val))
            let start := BitProgram.initial driver (encodeBTNInstance desc G β P ℓ')
            ∃ (n : ℕ) (z : BitProgram.Cfg r s l), BitProgram.Trace driver n start z ∧ z.pc=none ∧
              z.stacks out=w ∧ z.stacks driver.outputStack=[true] ∧ (n:ℝ)≤(polyBound K (β+desc.length) * (Told : ℝ) * (2 : ℝ)^((K : ℝ) *
                ((β : ℝ)/Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ+1),
                 ((β : ℝ)/(8 : ℝ)^d) / Real.sqrt ((ρ : ℝ)/(2 : ℝ)^d)))) ∧
              ∀ j c,j≤n→ BitProgram.Trace driver j start c→∀ i,(c.stacks i).length≤K*(β+desc.length+1)^K := by sorry

end DetDLP
