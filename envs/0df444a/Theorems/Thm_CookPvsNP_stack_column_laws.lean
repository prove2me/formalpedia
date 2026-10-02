-- Prove2me | Theorems.Thm_CookPvsNP_stack_column_laws
-- name    : CookPvsNP.stack_column_laws
-- status  : Open
-- author  : @arexychen
-- created : 2026-10-02T11:01:33.243985+00:00
-- url     : https://prove2.me/theorems/616dcab4-566f-4102-8c67-d7506c1ca37d
-- title:
--   Column sweeps implement keep, push, and pop
-- statement:
--   The forward sweep followed by the backward sweep adds exactly one column. Projection onto any stack is respectively the old padded list followed by a blank, a new symbol prepended to the old list, or the tail of the old list followed by two padding blanks.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackModel

namespace CookPvsNP
theorem stack_column_laws {K A : Type} (a : K → StackAct A)
    (r : List (StackCol K A)) (k : K) :
    let r' := stackBackward a (stackForward a (stackPushCarry a) r)
    r'.length = r.length + 1 ∧
    r'.map (fun (v : StackCol K A) => v k) =
      match a k with
      | .keep => r.map (fun (v : StackCol K A) => v k) ++ [none]
      | .push b => some b :: r.map (fun (x : StackCol K A) => x k)
      | .pop => (r.map (fun (v : StackCol K A) => v k) ++ [none]).tail ++ [none] := by sorry
end CookPvsNP
