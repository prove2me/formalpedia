-- Prove2me | Theorems.Thm_CircletTSP_Facet_theorem_3_1
-- name    : CircletTSP.Facet.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:15.572556+00:00
-- url     : https://prove2.me/theorems/a98da629-b026-4ddc-9ec4-b01fed1d7a60
-- title:
--   Theorem 3.1, p. 8 — the circlet inequalities are valid
-- statement:
--   Let $n$ be a positive multiple of $4$, $d=n/2$, and for $1\le i\le d$ let
--   $$c_i=\begin{cases} i, & i \text{ odd},\\ d-i, & i \text{ even}.\end{cases}$$
--   Then every Hamiltonian cycle $H$ on $K_n$, with incidence vector $x=\chi_H$ and length counts $t_i$, satisfies
--   $$\sum_{i=1}^{d} c_i t_i\ \ge\ n-2. \tag{2}$$
--   That is, the circlet inequalities are valid.
--
--   Tight examples include the cycle $1,2,\dots,d,n,n-1,\dots,d+1$, which uses two edges of length $d$ and $n-2$ edges of length $1$.
--
--   **Formalization Note** "A feasible TSP input" is read as the incidence vector of a Hamiltonian cycle, the object of the paper's proof; validity on all of $STSP(n)$ follows by linearity and is part of the goal theorem. $0<n$ is added: for $n=0$ the inequality holds trivially but the goal's facet statement fails.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 8, Theorem 3.1, Inequality (2)

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Theorem 3.1 (p. 8): for `n` divisible by `4`, every Hamiltonian cycle on `n` cities satisfies
Inequality (2), `∑_{i=1}^{d} c_i t_i ≥ n - 2`; the circlet inequalities are valid. -/
theorem theorem_3_1 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) :
    (n : ℝ) - 2 ≤ circletForm n (MetricTSP.tourVec π) := by sorry

end CircletTSP.Facet
