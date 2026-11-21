-- Prove2me | Theorems.Thm_AutoformalisationSCI_theorem_A_4
-- name    : AutoformalisationSCI.theorem_A_4
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:34:52.410807+00:00
-- url     : https://prove2.me/theorems/13e8f729-dbbf-4183-acb6-457740b2407a
-- title:
--   Theorem A.4 — $\Sigma^0_l$-completeness of $d_l$
-- statement:
--   **Theorem A.4** (p. 21). Fix integers $l\ge 2$ and $k\ge 9$. For **any** computable enumeration $(p_e)_{e\in\mathbb N}$ of all integer-coefficient polynomials in $l-1+k$ variables $(n,z_2,\dots,z_{l-1},x_1,\dots,x_k)$, let $B_e^{(l)}(n)$ be the alternating-quantifier predicate of Eq. (A.4), and let
--   $$d_l=\{e\in\mathbb N:(\exists n\in\mathbb N)\,B_e^{(l)}(n)\}.$$
--   Then $d_l$ is $\Sigma^0_l$-complete (under computable many-one reductions). In particular, $d_l$ is not Turing-reducible to $\emptyset^{(l-1)}$: no algorithm, even with an oracle for $\emptyset^{(l-1)}$, can always determine whether the least $n$ with $B_e^{(l)}(n)$ is well-defined.
--
--   This generalises Theorem A.3 to arbitrarily high finite levels of the arithmetical hierarchy while retaining the polynomial predicates and least-number construction of Example 4.1.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Theorem A.4, p. 21; Eq. (A.4), p. 20.

import Mathlib
import Definitions.Def_AutoformalisationSCI_Arith
import Definitions.Def_AutoformalisationSCI_Oracle
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem theorem_A_4 (l k : ℕ) (hl : 2 ≤ l) (hk : 9 ≤ k) (E : ComputablePolyEnum (l - 1 + k)) :
    SigmaComplete l (dSetL l k hl E) ∧
      ¬ SetTuringReducible (dSetL l k hl E) (jumpIter (l - 1)) := by sorry

end AutoformalisationSCI
