-- Prove2me | Theorems.Thm_CookPvsNP_stack_trace_laws
-- name    : CookPvsNP.stack_trace_laws
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:36:45.728664+00:00
-- url     : https://prove2.me/theorems/4e1e8c9c-2cdc-4cb5-ac48-b8f89c95b42a
-- title:
--   stack trace laws
-- statement:
--   Stack traces compose, map along a step-preserving nonhalting configuration map, and imply the corresponding machine iterate.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram
open CookPvsNP

namespace CookPvsNP
theorem stack_trace_laws {K A Q : Type} (P : StackMachine K A Q) :
    (∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → (P.step^[n]) c = d) ∧
    (∀ {n m : ℕ} {c d e : StackCfg K A Q}, StackTrace P n c d → StackTrace P m d e →
      StackTrace P (n + m) c e) ∧
    (∀ {R : Type} (S : StackMachine K A R) (f : StackCfg K A Q → StackCfg K A R),
      (∀ c, P.done c.state = false → S.done (f c).state = false ∧ S.step (f c) = f (P.step c)) →
      ∀ {n : ℕ} {c d : StackCfg K A Q}, StackTrace P n c d → StackTrace S n (f c) (f d)) := by sorry
end CookPvsNP
