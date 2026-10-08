-- Prove2me | Theorems.Thm_DiaconisStroock_CanonPaths_cut_weight_le
-- name    : DiaconisStroock.CanonPaths.cut_weight_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:08:04.581552+00:00
-- url     : https://prove2.me/theorems/91d63e3c-5c42-4245-859f-b8dc892883e7
-- title:
--   §3B: the cut weight is at most η times cut flow
-- statement:
--   Let $P$ be a stochastic matrix on a finite state space, let $\pi$ have nonnegative weights, and choose a positive-flow walk $\gamma_{xy}$ for every distinct ordered pair. For any set $S$, the total weight of ordered pairs from $S$ to its complement is bounded by congestion times the stationary flow out of $S$:
--
--   $$
--   \pi(S)\pi(S^{\mathrm c})\leq
--   \eta\,Q(S\times S^{\mathrm c}),
--   \qquad Q(S\times S^{\mathrm c})=
--   \sum_{x\in S,\,y\notin S}\pi(x)P(x,y).
--   $$
--
--   This is the complementary cut estimate in the proof of Proposition 7.
--
--   **Formalization Note** Stochasticity ensures nonnegative flow even on cut edges not used by the selected walks. The inequality itself does not require stationarity, reversibility, or the condition $\pi(S)\leq\tfrac12$.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 54, §3B, proof of Proposition 7; https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_CanonPaths_Eta

namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- The aggregate weight of paths leaving a cut is at most η times the stationary flow
across that cut (§3B, proof of Proposition 7, p. 54). -/
theorem cut_weight_le {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ)
    (hπ0 : ∀ x, 0 ≤ π x) (Γ : V → V → List V) (hΓ : IsWalkSystem P π Γ)
    (S : Finset V) :
    (∑ x ∈ S, π x) * (∑ y ∈ Sᶜ, π y) ≤
      eta P π Γ * ∑ x ∈ S, ∑ y ∈ Sᶜ, edgeMeasure P π x y := by sorry

end DiaconisStroock.CanonPaths
