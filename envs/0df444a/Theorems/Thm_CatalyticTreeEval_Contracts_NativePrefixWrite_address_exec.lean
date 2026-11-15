-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_NativePrefixWrite_address_exec
-- name    : CatalyticTreeEval.Contracts.NativePrefixWrite.address_exec
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T12:53:56.24664+00:00
-- url     : https://prove2.me/theorems/1f086a3e-7c7d-45da-ae52-0579e2dd263b
-- title:
--   Charged native write to a runtime-selected work-prefix cell
-- statement:
--   For valid physical head positions $p$ and $q$, the finite native machine writes a chosen bit $b$ to work position $p$, returns both read-only heads to origin, and leaves the work head at
--
--   $$p+q.$$
--
--   If the initial work position is $h$, every transition is charged and the exact running time is
--
--   $$(h+1)+(p+1)+1+(q+1).$$
--
--   The work-head envelope is bounded by any $B$ exceeding both $h$ and $p+q$. The catalyst-head interval is $[0,q+1)$, independent of the length of an unused catalytic suffix. Every work cell other than $p$, the complete catalyst, and prior output are preserved at every prefix. The preconditions explicitly require the two head positions to be valid; preparing those distances from binary banks is a separate native computation.
--
--   The machine first returns the work head to origin using its actual origin sensor. It then repeatedly moves the input head left and the work head right until the input origin is reached. This transfers the physical distance $p$ into the work-head position without remembering it in the finite controller. A single transition writes the pending bit. Repeating the same transfer with the catalyst head adds the distance $q$ and returns that head to origin. The four components are composed with the native first-exit sequencing theorem; there is no uncharged jump or address conversion.
--
--   Each distance-transfer scan has one state. Before its final origin test, each transition decreases the remaining distance by one and increases the work position by one. Induction gives the complete trajectory, exact first halt, and preservation of every tape bit. Native sequential composition combines the trajectory frames. Inspection of the combined transition table shows that the catalyst never moves right, which supplies the catalyst bound for every successful prefix.
--
--   This is supporting native-machine infrastructure for the input/output hosts and dense query-prefix handling in the Catalytic Tree Evaluation formalisation. It is not a claim that the full evaluator or the headline theorem has been completed.
-- source:
--   Original native-machine auxiliary lemma supporting Section 4 of Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/abs/2602.14320. Formal source: https://github.com/sragavan99/lean-prove2me-fills/tree/codex/catalytic-tree-evaluation/Solutions/CatalyticTreeEvaluation. The prepared real-head positions are explicit preconditions; their setup is a separately charged computation.

import Definitions.Def_CatalyticTreeEval_NativePrefixAddress
set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativePrefixWrite

theorem address_exec (bit : Bool) (input : List Bool)
    (c : Config (machine bit)) (bound : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (hb : c.workHead < bound) (hsum : c.inputHead+c.catalystHead < bound) :
    ∃ d : Config (machine bit),
      FirstExit ((machine bit).step input)
        (fun _ e => (Envelope.mk 0 bound 0 (c.catalystHead+1)).Contains e ∧
          SameOutside ⟨{c.inputHead},∅⟩ c e)
        {e | e.state=none} {c with state:=some (machine bit).start} d (time c) ∧
      d.inputHead=0 ∧ d.catalystHead=0 ∧
      d.workHead=c.inputHead+c.catalystHead ∧
      d.work=Function.update c.work c.inputHead bit ∧
      d.catalyst=c.catalyst ∧ d.output=c.output := by sorry

end CatalyticTreeEval.Contracts.NativePrefixWrite
