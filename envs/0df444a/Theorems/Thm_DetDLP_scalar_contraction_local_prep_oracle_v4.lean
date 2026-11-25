-- Prove2me | Theorems.Thm_DetDLP_scalar_contraction_local_prep_oracle_v4
-- name    : DetDLP.scalar_contraction_local_prep_oracle_v4
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T03:59:23.911903+00:00
-- url     : https://prove2.me/theorems/aff1cf0d-101b-44f9-af87-c59f1173f7d8
-- title:
--   Oracle preparation program with a uniform step bound
-- statement:
--   There is one preparation program, determined by the fixed port evaluator $Q$, with a uniform cost. For every external budget $L$ there is a degree $K$ such that the following holds for every scalar-contraction instance. Whenever $Q$ returns every port tensor of $A$ in at most $8\cdot\mathrm{Told}$ steps, inside the stated stack bound, the program starts from the canonical encoding of $(\mathrm{desc},G,\beta,P,\ell')$ and halts in the packed frame whose context slot $0$ is the bit-list of the folded contraction word, with every register set. The number of steps is at most
--   $$\mathrm{polyBound}(K,\beta+|\mathrm{desc}|)\cdot\mathrm{Told}\cdot 2^{K\cdot E(\beta,G)},$$
--   where $E(\beta,G)$ is the degree-sensitive exponent of the local contraction, and the scratch-stack bound is at most $K(\beta+|\mathrm{desc}|+1)^K$.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026, Section 5.2. Corrected local-instruction packaging: preparation depends on the port oracle, and the stepper step and stack bounds are existential and linear in the answer length.

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open DetDLP.ContinuationSchedule OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation

/-- One prep program, using the port oracle `Q`, writes the contraction word with a uniform step bound. -/
theorem scalar_contraction_local_prep_oracle_v4
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov) :
    ∃ (s lp : ℕ) (hs : 0 < s) (prep : BitProgram.Program 8 (20 + s) lp),
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
            cap0 ≤ K * (β + desc.length + 1) ^ K := by sorry

end DetDLP
