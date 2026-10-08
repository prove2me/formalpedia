-- Prove2me | Theorems.Thm_Dubey1986_Inefficiency_finite_of_transverse
-- name    : Dubey1986.Inefficiency.finite_of_transverse
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:34:40.843985+00:00
-- url     : https://prove2.me/theorems/e751d027-576b-43f8-affd-1f3ac923bef0
-- title:
--   p. 6, ¶1 — if $D_u$ is transverse to $N^*$, then $S\cap D_u^{-1}(N^*)$ and the interior Nash equilibria are finite
-- statement:
--   Let $n\ge2$, $k(i)\ge1$, let $V^i\supseteq S^i$ be open, let $\underline V^i$ be compact with $S^i\subseteq\operatorname{Int}\underline V^i$, $\underline V^i\subseteq V^i$, and let $u\in(U)^n$ be a game such that $D_u$ is transverse to $N^*$ at every point of $\underline V=\underline V^1\times\dots\times\underline V^n$. Then
--   1. the set $S\cap D_u^{-1}(N^*)$ is finite;
--   2. the set of Nash equilibria $s$ of $u$ with every $s^i$ in the interior of $S^i$ is finite.
--
--   Since $\dim V=r(n)=\operatorname{codim}N^*$, transversality makes $D_u^{-1}(N^*)$ discrete, and its intersection with the compact $S$ is finite; by (i) the interior Nash equilibria lie in it.
--
--   **Formalization Note** The paper writes "By (i), $N(u)\subset S\cap D_u^{-1}(N^*)$"; (i) was established for interior points only, so part 2 is stated for the interior Nash equilibria, which is the case under consideration at that point of the proof.
-- source:
--   Dubey, Inefficiency of Nash Equilibria, IIASA WP-83-74 (July 1983), p. 6, first paragraph

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

namespace Dubey1986.Inefficiency

theorem finite_of_transverse {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℕ) (hk : ∀ i, 1 ≤ k i)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (hSV : ∀ i, simplex (k i) ⊆ V i) (W : ∀ i, Set (Fin (k i) → ℝ))
    (hWc : ∀ i, IsCompact (W i)) (hSW : ∀ i, simplex (k i) ⊆ interior (W i))
    (hWV : ∀ i, W i ⊆ V i) (u : Fin n → Strat k → ℝ) (hu : IsGame V u)
    (htr : ∀ x ∈ Set.univ.pi W, TransverseAt (Dmap u) (Nstar k) x) :
    (S k ∩ Dmap u ⁻¹' (Nstar k : Set (Fin n → (Strat k →L[ℝ] ℝ)))).Finite ∧
    {s | s ∈ NashSet u ∧ ∀ i, s i ∈ interior (simplex (k i))}.Finite := by sorry

end Dubey1986.Inefficiency
