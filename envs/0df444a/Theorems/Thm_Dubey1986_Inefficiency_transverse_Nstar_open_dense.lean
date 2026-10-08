-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_transverse_Nstar_open_dense
-- name    : Dubey1986.Inefficiency.transverse_Nstar_open_dense
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:46.061601+00:00
-- url     : https://prove2.me/theorems/a5312d02-60c0-48de-b9fb-fee6af5d45c8
-- title:
--   p. 5, (*) for $M=N^*$ — generically $D_u$ is transverse to $N^*$ on a compact neighbourhood of $S$
-- statement:
--   Let $n\ge2$, $k(i)\ge1$, let $V^i\supseteq S^i$ be open, and fix compact sets $\underline V^i$ with $S^i\subseteq\operatorname{Int}\underline V^i$ and $\underline V^i\subseteq V^i$. Then there is an open dense set $U_{N^*}$ of $(U)^n$ such that for every $u\in U_{N^*}$ the map $D_u$ is transverse to $N^*$ at every point of
--   $$\underline V=\underline V^1\times\dots\times\underline V^n .$$
--
--   This is claim (*) of the proof for the submanifold $M=N^*$, the input to the finiteness of Nash equilibria.
--
--   **Formalization Note** The paper states (*) for an arbitrary submanifold $M$ of $\mathbb R^{n\times r(n)}$; it is stated here for the linear subspace $N^*$ only, which needs no notion of submanifold.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 5, claim (*) with M = N*

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem transverse_Nstar_open_dense {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ)
    (hk : ∀ i, 1 ≤ k i) (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (W : ∀ i, Set (Fin (k i) → ℝ))
    (hWc : ∀ i, IsCompact (W i)) (hSW : ∀ i, simplex (k i) ⊆ interior (W i))
    (hWV : ∀ i, W i ⊆ V i) :
    ∃ UM : Set (Fin n → Strat k → ℝ), IsOpenDense V UM ∧
      ∀ u ∈ UM, ∀ x ∈ Set.univ.pi W, TransverseAt (Dmap u) (Nstar k) x := by sorry

end Dubey1986.Inefficiency
