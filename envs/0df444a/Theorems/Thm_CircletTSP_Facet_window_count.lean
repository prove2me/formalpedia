-- Prove2me | Theorems.Thm_CircletTSP_Facet_window_count
-- name    : CircletTSP.Facet.window_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:12.754131+00:00
-- url     : https://prove2.me/theorems/ba8d0ce3-43c5-4d3f-ba83-7ecf094b401e
-- title:
--   Proof of Theorem 3.1, p. 12 — t₁ + 2t_d = T₁ + T₂ + ⋯ + T_d
-- statement:
--   Let $n=2d$ be a positive multiple of $4$ and $H$ a Hamiltonian cycle on $K_n$. Then
--   $$t_1+2t_d=T_1+T_2+\dots+T_d,$$
--   where $T_u$ is the number of edges of $H$ among $\{u,u+1\},\{u+d,u+d+1\},\{u,u+d\},\{u+1,u+1+d\}$, the edges of the window $W_u=\{u,u+1,u+d,u+1+d\}$ of length $1$ or $d$.
--
--   Each edge of length $1$ lies in exactly one of the windows $W_1,\dots,W_d$ and each edge of length $d$ in exactly two, so rotating the window $d$ times counts $t_1+2t_d$.
--
--   **Formalization Note** The windows $u=1,\dots,d$ are the 0-based vertices $0,\dots,d-1$.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, pp. 11–12, proof of Theorem 3.1

import Mathlib
import Definitions.Def_MetricTSP_tour_vector
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Proof of Theorem 3.1 (p. 12): for a Hamiltonian cycle on `n = 2d` vertices,
`t₁ + 2 t_d = T₁ + T₂ + ⋯ + T_d`, where `T_u` counts the edges of the cycle inside the window
`{u, u + 1, u + d, u + 1 + d}` (the windows `u = 1, …, d` are the 0-based `u = 0, …, d - 1`). -/
theorem window_count (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) (π : Equiv.Perm (Fin n)) :
    lenCount n 1 (MetricTSP.tourVec π) + 2 * lenCount n (n / 2) (MetricTSP.tourVec π) =
      ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.val < n / 2), window π u := by sorry

end CircletTSP.Facet
