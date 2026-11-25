-- Prove2me | Theorems.Thm_DetDLP_exhaustive_scalar_contraction_leaf_machine
-- name    : DetDLP.exhaustive_scalar_contraction_leaf_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T19:36:11.933167+00:00
-- url     : https://prove2.me/theorems/c91f303a-e1f7-4913-8731-2706fffd0c9a
-- title:
--   Uniform exhaustive scalar leaf machine with polynomial workspace
-- statement:
--   Given any primitive tensor-entry evaluator, construct a single finite Boolean-stack program for the leaves of scalar contraction. From the explicit packed graph and counters it computes a packed integer whose digits encode the entire requested truncated contraction. It handles every edge assignment and queries each vertex on its incident bits in graph order. Its time is bounded by two to the edge count times a polynomial times the per-entry evaluation time plus one. Every intermediate stack has polynomial length independently of the entry evaluation time.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.2, the direct summation at scalar recursion leaves.

import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation Finset Polynomial

namespace DetDLP

theorem exhaustive_scalar_contraction_leaf_machine (E : PrimitiveMachine) (out : Fin E.tapeCount) :
    ∃ (s l K : ℕ) (M : BitProgram.Program 8 (19+(7+s)) l),
      ∀ (G : BipartiteMultigraph) (P ell : ℕ) (desc : List Bool)
        (A : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→Fin ell→ℕ)
        (T U : ℕ),0<P → 0<ell → (∀ v t i,A v t i<2^P) →
        (∀ v t,RunsWithin E out (encodePortQuery desc v.val (List.ofFn t))
          (encodeNatListBin (List.ofFn (A v t))) T U) →
        let w := G.nE+G.nV*(P+Nat.clog 2 ell)+1+P
        let r := G.nV+3
        let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
        let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
        let frame := Fin.addCases (m:=8) (n:=11) (fun _ => ([]:List Bool))
          (fun j => ((![2^G.nE,G.nV,0,0,1,0,0,0,1,1,2^G.nE] : Fin 11→ℕ) j).bits)
        let metadata : Fin 7→List Bool := ![desc,r.bits,code.bits,(code/r).bits,(2^w-1).bits,(2^w).bits,(2^w-1-2).bits]
        let input := Fin.addCases frame (Fin.addCases metadata (fun _ : Fin s => ([]:List Bool)))
        let cap := K*(G.nE+G.nV+desc.length+P+ell+(U+8)+1+1)^K
        let Z := BTNContract G (fun v t => ∑ i : Fin ell,monomial i.val (A v t i:ℤ))
        ∀ reg : Fin 8→Bool,
        let start : BitProgram.Cfg 8 (19+(7+s)) l := ⟨some M.entry,reg,input⟩
        ∃ (z steps : ℕ) (rf : Fin 8→Bool) (o : Fin (19+(7+s))→List Bool),steps ≤ 2^G.nE*(8*T+1)*cap ∧
          BitProgram.Trace M steps start ⟨none,rf,o⟩ ∧
          (∀ j c,j ≤ steps → BitProgram.Trace M j start c → ∀ i,(c.stacks i).length ≤ cap) ∧
          o ((13:Fin 19).castAdd (7+s))=z.bits ∧
          encodeNatListBin (List.ofFn fun i : Fin ell => z/(2^w)^i.val%(2^w)%(2^P))=
          encodeNatListBin (List.ofFn fun i : Fin ell => (Z.coeff i.val:ZMod (2^P)).val) := by sorry

end DetDLP
