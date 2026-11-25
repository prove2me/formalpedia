-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_prep_program_v4
-- name    : DetDLP.scalar_contraction_local_prep_program_v4
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T04:05:40.139192+00:00
-- url     : https://prove2.me/theorems/4a74bd9b-5c5b-4649-87ca-09c2a119fce9
-- title:
--   Oracle preparation of the contraction word
-- statement:
--   There is a single 8-register preparation program, depending only on the port oracle $Q$, together with a positive number of context stacks.
--
--   Consider a bipartite Boolean tensor network whose size is bounded by $C,c_0,\beta$, and whose coefficient tensor $A$ is exactly the tensor returned by $Q$ on encoded port queries. Starting from the canonical encoding of $(\mathrm{desc},G,\beta,P,\ell')$, the program halts in the packed root frame. Context slot $0$ holds the bits of the folded encoding of the contracted coefficient vector. The numeric frame is the usual one: base $q=B+1$, the constant $1$, and root indices $(a,b,\mathrm{stack})=(0,0,1)$.
--
--   The step count and the stack cap are existential. The cap has to cover the whole frame, including the constant bit-list $(1).\mathsf{bits}$ on stack $9$ and the bits of $q$. It is not identified with a bound that only controls the context.
-- source:
--   DetDLP Lemma 5.2 / Theorem 3.1, private mission correction of the local instruction packaging

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- One preparation machine for the port oracle `Q`. The contracted word is a
function of that oracle, so the machine is only required on tensors `Q` actually
returns. Step count and stack cap are existential: the packed frame stores
`(1).bits` and `q.bits`, which need not fit in a context-only bound. -/
theorem scalar_contraction_local_prep_program_v4
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
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
        ∃ (prepSteps cap0 : ℕ),
          BitProgram.Trace prep prepSteps start ⟨none, reg, pack 0 0 1 0 0 0⟩ ∧
            (∀ j c, j ≤ prepSteps → BitProgram.Trace prep j start c →
              ∀ i, (c.stacks i).length ≤ cap0) := by sorry

end DetDLP
