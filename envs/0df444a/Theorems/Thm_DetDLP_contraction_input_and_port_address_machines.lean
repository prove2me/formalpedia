-- Prove2me | Theorems.Thm_DetDLP_contraction_input_and_port_address_machines
-- name    : DetDLP.contraction_input_and_port_address_machines
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T18:10:57.609805+00:00
-- url     : https://prove2.me/theorems/3b96bee2-b744-4693-be8e-472943522276
-- title:
--   Polynomial-time stack programs for contraction input and ordered local port queries
-- statement:
--   Decode a raw binary tensor-network instance with a fixed Boolean-stack table into its description, graph metadata, ordered endpoint stream, precision and truncation. Convert the endpoint stream into a sentinel-terminated mixed-radix word. A third fixed program computes the exact port assignment of any vertex by selecting the appropriate bits of a global assignment in increasing original edge order, including isolated vertices and parallel edges. The three time bounds are explicit polynomials in the stated input dimensions.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5, executable preparation of scalar tensor entry queries.

import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false
open OAI.Algorithms.SubexponentialSAT

namespace DetDLP

theorem contraction_input_and_port_address_machines :
    ∃ (l₁ l₂ l₃ K : ℕ) (read : BitProgram.Program 8 31 l₁) (pack : BitProgram.Program 8 31 l₂)
      (project : BitProgram.Program 8 24 l₃),∀ (G : BipartiteMultigraph) (desc : List Bool) (β P ell : ℕ),
      let xs := encodeBTNInstance desc G β P ell
      let endpoints := (List.finRange G.nE).flatMap fun e => [(G.endpoints e).1.val,(G.endpoints e).2.val]
      let es := encodeNatListBin endpoints
      let radix := G.nV+3
      let code := Nat.ofDigits radix endpoints+radix^(2*G.nE)
      let W := (G.nV+4)*(2*G.nE+3)
      let word (s : List Bool) := s.foldr (fun b k => b.toNat+2*k) 1
      (∃ t rf o,t≤K*(xs.length+4)^3 ∧ BitProgram.Trace read t (BitProgram.initial read xs) ⟨none,rf,o⟩ ∧
        o 19=desc++[true] ∧ o 21=β.bits ∧ o 22=P.bits ∧ o 23=ell.bits ∧
        o 24=G.nV.bits ∧ o 25=G.nE.bits ∧ o 26=List.ofFn G.side++[true] ∧ o 27=es++[true] ∧
        ∀ j c,j≤t → BitProgram.Trace read j (BitProgram.initial read xs) c → ∀ i,(c.stacks i).length≤xs.length+t) ∧
      (∀ reg : Fin 8→Bool,let m := G.nV+2
        let v : Fin 23→ℕ := ![0,0,1,0,0,0,0,0,1,2,m,m+1,m-2,word es,0,1,0,0,0,(word es)%2,0,1,2]
        let s := Fin.addCases (m:=8) (n:=23) (fun _ => ([]:List Bool)) (fun j => (v j).bits)
        let start : BitProgram.Cfg 8 31 l₂ := ⟨some pack.entry,reg,s⟩
        ∃ t rf o,t≤K*(2*G.nE+1)*(es.length+4)*(W+es.length+5)^2 ∧
          BitProgram.Trace pack t start ⟨none,rf,o⟩ ∧ o pack.outputStack=code.bits) ∧
      ∀ (v : Fin G.nV) (k : ℕ),k<2^G.nE → ∀ reg : Fin 8→Bool,
        let s : Fin 16→ℕ := ![v.val+1,radix,code,k,0,1,1,2,code/radix,0,0,0,0,0,0,0]
        let start : BitProgram.Cfg 8 24 l₃ := ⟨some project.entry,reg,Fin.addCases (m:=8) (n:=16)
          (fun _ => ([]:List Bool)) (fun j => (s j).bits)⟩
        ∃ t rf o,t≤K*(G.nE+1)*(W+4)^2 ∧ BitProgram.Trace project t start ⟨none,rf,o⟩ ∧
          o project.outputStack=(List.ofFn fun j => k.testBit ((G.ports v).get j).val)++[true] := by sorry
end DetDLP
