-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_adaptive_schedule
-- name    : DetDLP.scalar_contraction_adaptive_schedule
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T09:10:26.264581+00:00
-- url     : https://prove2.me/theorems/2256e5e7-baf7-4328-b88a-b8184d91d62e
-- title:
--   Adaptive contraction schedule and Computes witness
-- statement:
--   Under bounded port-evaluator hypotheses, build buffers and a map F with Computes witness for the scalar contraction word.
-- source:
--   DetDLP Section 5.2

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_packed_scalar_leaf_contraction_scan
import Theorems.Thm_DetDLP_edge_partition_by_local_labeling
import Theorems.Thm_DetDLP_active_scalar_packet_recursion_node

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem scalar_contraction_adaptive_schedule
    (C c0 : ℕ) (hC : 0<C) (hc0 : 0<c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it≠iv) (ho : ot≠ov)
    (s : ℕ)
    (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
    (hβ : 2 ≤ β) (ht : 1 ≤ Told) (he : G.nE ≤ C * β) (hv : G.nV ≤ β ^ c0)
    (hP₁ : 1 ≤ P) (hP₂ : P ≤ C * β) (hl₁ : 1 ≤ ℓ') (hl₂ : ℓ' ≤ C * β)
    (ha : ∀ v t i, A v t i < 2^P)
    (ev : ∀ v t (regs : Fin 3→Bool),
      let q := (encodePortQuery desc v.val (List.ofFn t)).tail
      let start : BitProgram.Cfg 3 se le := ⟨some Q.entry,regs,fun j =>
        if j=it then List.replicate q.length true else if j=iv then q else []⟩
      ∃ (n : ℕ) (c : BitProgram.Cfg 3 se le), n≤8*Told ∧ BitProgram.Trace Q n start c ∧
        c.pc=none ∧ ((((c.stacks ot).zip (c.stacks ov)).takeWhile Prod.fst).map Prod.snd)=
          encodeNatListBin (List.ofFn (A v t)) ∧
        ∀ j b,j≤n→ BitProgram.Trace Q j start b→∀ i,(b.stacks i).length≤(β+desc.length)^c0+8) :
    let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
    let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
    let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
      Polynomial.monomial i.val (A v t i : ℤ))
    let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
      ((Z.coeff i.val : ZMod (2^P)).val))
    let word := w.foldr (fun b z => b.toNat+2*z) 1
    ∃ (context : Fin s→List Bool) (F : ℕ→ℕ→Answer) (B T U x y calls depth cap0 prepSteps : ℕ)
      (reg : Fin 8→Bool),
      0<B ∧ (∀ i,(context i).length≤U) ∧
      Computes F B x y word calls depth ∧ reg 1=true := by sorry

end DetDLP
