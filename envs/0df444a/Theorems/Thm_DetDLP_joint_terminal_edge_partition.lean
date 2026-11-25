-- Prove2me | Theorems.Thm_DetDLP_joint_terminal_edge_partition
-- name    : DetDLP.joint_terminal_edge_partition
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:55.656394+00:00
-- url     : https://prove2.me/theorems/824849ca-5d9a-463e-b5c9-47ec1099be8a
-- title:
--   Simultaneous balancing of real edge ports and terminal legs
-- statement:
--   Let a bipartite multigraph with $M$ edges and maximum degree $\Delta$ carry $b$ terminal legs, with at most $\tau$ on each occupied host. Give each vertex an $a$-digit label over an alphabet of size $s$, and let $q=s^a$. For any integral nonnegative weights $w,v$, one can deterministically choose labels with
--   $$sq^2\left(w\sum_c X_c^2+v\sum_{i,g}Y_{i,g}^2\right)\le sw(M^2+2M\Delta q^2)+vabq^2(b+s\tau).$$
--   Here $X_c$ counts edges in the ordered endpoint-label cell $c$, and $Y_{i,g}$ counts terminal legs whose host has digit $g$ in position $i$. The same labels control both quantities.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.1, simultaneous terminal and scalar port balance in the one-step factorization.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

theorem joint_terminal_edge_partition (G : BipartiteMultigraph) (s : ℕ) [NeZero s] (a : ℕ)
    {b : ℕ} (host : Fin b → Fin G.nV) (τ w v : ℕ)
    (ht : ∀ x, (Finset.univ.filter fun y => host x = host y).card ≤ τ) :
    let q := s^a
    let l := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
    let r := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2
    ∃ L : Fin G.nV → Fin q,
      let X := fun c : Fin q × Fin q => ∑ e : Fin G.nE, if (L (l e),L (r e)) = c then 1 else 0
      let Y := ∑ i : Fin a, ∑ x : Fin b, ∑ y : Fin b,
        if finFunctionFinEquiv.symm (L (host x)) i = finFunctionFinEquiv.symm (L (host y)) i then 1 else 0
      s*q^2*(w*(∑ c, (X c)^2) + v*Y) ≤
        s*w*(G.nE^2+2*G.nE*G.maxDeg*q^2) + v*a*b*q^2*(b+τ*s) := by sorry
end DetDLP
