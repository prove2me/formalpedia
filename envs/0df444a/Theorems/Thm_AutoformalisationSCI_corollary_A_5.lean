-- Prove2me | Theorems.Thm_AutoformalisationSCI_corollary_A_5
-- name    : AutoformalisationSCI.corollary_A_5
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T15:35:48.98776+00:00
-- url     : https://prove2.me/theorems/3476c862-f955-4aa1-9611-1cda377dbacf
-- title:
--   Corollary A.5 — SCI of $d_l$ is exactly $l$
-- statement:
--   **Corollary A.5** (p. 22). For each $l\ge 2$ and $k\ge 9$, let $\Xi_{d_l}:\mathbb N\to\{0,1\}$ be the decision problem of the set $d_l$ (i.e. $\Xi_{d_l}(e)=1$ iff $e\in d_l$). With the enumeration of Theorem A.4,
--   $$\mathrm{SCI}_A(\Xi_{d_l})=l\qquad\text{for every }l\ge 2.$$
--   Equivalently, the decision problem for $d_l$ lies in $\Delta^A_{l+1}\setminus\Delta^A_l$.
--
--   This transfers the $\Sigma^0_l$-completeness of $d_l$ (Theorem A.4) into an exact Solvability Complexity Index, using that the SCI hierarchy generalises the arithmetical hierarchy (Remark A.2). It is the key input to the main SCI = ∞ conclusion.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), https://arxiv.org/abs/2610.08144. Corollary A.5, p. 22; Remark A.2, p. 19.

import Mathlib
import Definitions.Def_AutoformalisationSCI_SCI
import Definitions.Def_AutoformalisationSCI_Poly

open AutoformalisationSCI

namespace AutoformalisationSCI

theorem corollary_A_5 (l k : ℕ) (hl : 2 ≤ l) (hk : 9 ≤ k) (E : ComputablePolyEnum (l - 1 + k)) :
    SCI_A (setProblem (dSetL l k hl E)) = (l : WithTop ℕ) := by sorry

end AutoformalisationSCI
