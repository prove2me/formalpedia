-- Prove2me | Theorems.Thm_DetDLP_packed_hermite_normal_form_machine
-- name    : DetDLP.packed_hermite_normal_form_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T13:59:46.016794+00:00
-- url     : https://prove2.me/theorems/c8c77506-6526-4151-a763-62dc59ab122d
-- title:
--   A polynomial-time bit machine computes the full packed column Hermite form
-- statement:
--   A single finite Boolean-stack program computes bounded column Hermite normal form for every modulus $m\ge2$, every height $n$, and every finite collection of input columns. The initial words give the modulus, the row radix and the packed table of input columns reduced modulo $m$. The output word encodes all columns of the executable integer Hermite normal form, including their order and trailing zero entries. For an absolute exponent $k$ the full trace has at most $(n+\#\mathrm{cols}+\lceil\log_2m\rceil+4)^k$ instructions.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 4.3, uniform implementation of every elimination row and both column passes in the bordered Hermite computation.

import Definitions.Def_DetDLP_BorderedHermite
import Definitions.Def_OAIQ081S067

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT

namespace DetDLP

theorem packed_hermite_normal_form_machine :
    ∃ (l k : ℕ) (P : BitProgram.Program 8 55 l),
      ∀ (m n : ℕ) [NeZero m], 2 ≤ m →
      ∀ (cols : Array (BorderedHermite.Column n)) (r : Fin 8 → Bool),
        let b := m+1
        let D := b^n
        let serialize (a : Array (BorderedHermite.Column n)) :=
          Nat.ofDigits D ((a.toList.map fun v => Nat.ofDigits b
            (List.ofFn fun i => (v.get i).toNat))++[1])
        let reduced := cols.map (fun c => c.map (·%(m:ℤ)))
        let ports : Fin 9 → ℕ := ![m,b,D,1,1,serialize reduced,D/b,1,0]
        let start : Fin 55 → List Bool := fun i => Fin.addCases (m:=46) (n:=9)
          (fun _ => []) (fun j => (ports j).bits) i
        ∃ (t : ℕ) (f : BitProgram.Cfg 8 55 l),
          BitProgram.Trace P t ⟨some P.entry,r,start⟩ f ∧ f.pc=none ∧
          f.stacks P.outputStack=(serialize (BorderedHermite.normalForm (m:ℤ) cols)).bits ∧
          t ≤ (n+cols.size+bitLen m+4)^k := by sorry

end DetDLP
