-- Prove2me | Theorems.Thm_AutoformalisationSCI_theorem_A_3
-- name    : AutoformalisationSCI.theorem_A_3
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:34:23.0716+00:00
-- url     : https://prove2.me/theorems/b0c11afb-ea03-4efa-a172-bd80f9d4164b
-- title:
--   Theorem A.3 — $\Sigma^0_2$-completeness of $d$
-- statement:
--   **Theorem A.3** (p. 19). Fix an integer $k\ge 9$. For **any** computable enumeration $(p_e)_{e\in\mathbb N}$ of all integer-coefficient polynomials in $k+1$ variables, let $B_e(n)$ be the predicate that $p_e(n,x_1,\dots,x_k)\ne0$ for every $(x_1,\dots,x_k)\in\mathbb N^k$, and let
--   $$d=\{e\in\mathbb N:(\exists n\in\mathbb N)\,B_e(n)\}.$$
--   Then $d$ is $\Sigma^0_2$-complete (under computable many-one reductions). In particular, $d$ is not Turing-reducible to the halting problem $\emptyset'$: no algorithm, even with an oracle for the halting problem, can always determine whether the least number $n_e$ of Example 4.1 is well-defined.
--
--   This is the base case of the paper's hierarchy of presupposition-resolution problems and the precise form of the claim that resolving the ambiguity in Example 4.1 is harder than the halting problem.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Theorem A.3, p. 19; Eq. (A.3), p. 19; Example 4.1, p. 13.

import Mathlib
import Definitions.Def_AutoformalisationSCI_Arith
import Definitions.Def_AutoformalisationSCI_Oracle
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem theorem_A_3 (k : ℕ) (hk : 9 ≤ k) (E : ComputablePolyEnum (k + 1)) :
    SigmaComplete 2 (dSet k E) ∧ ¬ SetTuringReducible (dSet k E) (jumpIter 1) := by sorry

end AutoformalisationSCI
