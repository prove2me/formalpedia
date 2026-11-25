-- Prove2me | Theorems.Thm_DetDLP_terminal_packing_cell_bounds
-- name    : DetDLP.terminal_packing_cell_bounds
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T12:01:08.858234+00:00
-- url     : https://prove2.me/theorems/677cde66-35cc-4e24-b3bb-4aa4c39e4c5d
-- title:
--   Per-cell edge and terminal capacities for a single labeling
-- statement:
--   Let $M$ and $\Delta$ be the edge count and maximum internal degree of a bipartite network with $b>0$ terminal legs, at most $\tau$ per vertex. Let $q=64^a$ and assume $M\ge(a+2)q^4\Delta$ and $M\Delta>0$. There is one vertex labeling by $a$ base-64 digits for which every ordered endpoint-label cell has at most $2M/q^2$ real edges, and each group in every digit coordinate contains at most $b/32+16(a+2)\tau$ terminal legs.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Section 5.1, capacity bounds of Lemma 5.1(iii).

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false

namespace DetDLP

theorem terminal_packing_cell_bounds (G : BipartiteMultigraph) (a : ℕ) {b : ℕ} (host : Fin b → Fin G.nV) (τ : ℕ)
    (ht : ∀ x, (Finset.univ.filter fun y => host x = host y).card ≤ τ)
    (hb : 0 < b*τ) (hm : 0 < G.nE*G.maxDeg)
    (hsize : (a+2)*(64^a)^4*G.maxDeg ≤ G.nE) :
    let l := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).2 else (G.endpoints e).1
    let r := fun e : Fin G.nE => if G.side (G.endpoints e).1 then (G.endpoints e).1 else (G.endpoints e).2
    ∃ L : Fin G.nV → Fin (64^a),
      (∀ c : Fin (64^a) × Fin (64^a),
        (64^a)^2*(∑ e : Fin G.nE, if (L (l e),L (r e)) = c then 1 else 0) ≤ 2*G.nE) ∧
      (∀ (i : Fin a) (g : Fin 64),
        32*(∑ x : Fin b, if finFunctionFinEquiv.symm (L (host x)) i = g then 1 else 0) ≤ b+512*(a+2)*τ) := by sorry
end DetDLP
