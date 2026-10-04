-- Prove2me | Theorems.Thm_CookPvsNP_drop_polyTime
-- name    : CookPvsNP.drop_polyTime
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T17:13:52.244961+00:00
-- url     : https://prove2.me/theorems/4d6c6384-b0c3-45ca-8530-d16349104524
-- title:
--   Deleting a fixed prefix is polynomial-time computable
-- statement:
--   For every finite alphabet $A$ and every fixed natural number $n$, deleting the first $n$ letters is polynomial-time computable:
--   $$w\longmapsto\operatorname{drop}_n(w).$$
--   The result is empty if the input has fewer than $n$ letters. The machine and polynomial bound may depend on $n$, which is fixed rather than part of the input.
--
--   This elementary string transformation allows fixed headers to be removed when adapting encoded reductions.
--
--   **Formalization Note.** Computability uses the original Cook one-tape model, its output convention, and the deadline $|w|^k+k$.
-- source:
--   Auxiliary formalization lemma for Błażewicz, Lenstra and Rinnooy Kan (1983), Scheduling subject to resource constraints: classification and complexity, p. 15, Theorem 2, https://doi.org/10.1016/0166-218X(83)90012-4. Machine model: S. Cook, The P versus NP problem, Appendix.

import Definitions.Def_CookPvsNP_defs
set_option autoImplicit false

theorem CookPvsNP.drop_polyTime {A : Type} [Fintype A] [DecidableEq A] (n : ℕ) :
    CookPvsNP.PolyTimeComputable (fun w : List A => w.drop n) := by sorry
