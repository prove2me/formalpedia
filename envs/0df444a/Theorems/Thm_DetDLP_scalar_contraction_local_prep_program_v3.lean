-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_prep_program_v3
-- name    : DetDLP.scalar_contraction_local_prep_program_v3
-- status  : Disproved
-- author  : @Bingsheng
-- created : 2026-11-25T00:48:45.337747+00:00
-- url     : https://prove2.me/theorems/be2b07cb-9103-41f8-b4d9-b8deaf04ddd9
-- title:
--   Preparation microprogram (existential cap0)
-- statement:
--   Sound prep leaf with existential cap0 and word bits in context slot 0.
-- source:
--   DetDLP

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

theorem scalar_contraction_local_prep_program_v3
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
      ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
        (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
        2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
        1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
        (∀ v t i, A v t i < 2 ^ P) →
        let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
          Polynomial.monomial i.val (A v t i : ℤ))
        let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
          ((Z.coeff i.val : ZMod (2 ^ P)).val))
        let word := w.foldr (fun b z => b.toNat + 2 * z) 1
        let B := word + 1
        let q := B + 1
        let context : Fin s → List Bool := fun i => if i.val = 0 then word.bits else []
        let pack (a b stack tag arg save : ℕ) : Fin (20 + s) → List Bool :=
          let v : Fin 12 → ℕ := ![q, 1, 0, a, b, stack, tag, arg, save, 0, 0, 0]
          Fin.addCases (m := 20) (n := s)
            (Fin.addCases (m := 8) (n := 12) (fun _ => []) (fun j => (v j).bits)) context
        let start := BitProgram.initial prep (encodeBTNInstance desc G β P ℓ')
        let reg : Fin 8 → Bool := fun _ => true
        ∃ (prepSteps cap0 U : ℕ),
          (∀ i, (context i).length ≤ U) ∧
          BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
            (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
              ∀ i, (c.stacks i).length ≤ cap0) := by sorry

end DetDLP
