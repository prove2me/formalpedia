-- Prove2me | Theorems.Thm_DiaconisStroock_CanonPaths_bottleneckStar_ge
-- name    : DiaconisStroock.CanonPaths.bottleneckStar_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:59.081292+00:00
-- url     : https://prove2.me/theorems/b782636c-0c4f-4afb-82d9-91f2c8e60740
-- title:
--   §3B: the bottleneck constant satisfies h ≥ 1/(2η)
-- statement:
--   Let $P$ be a finite irreducible reversible Markov chain with at least two states and stationary distribution $\pi$. For a chosen positive-flow walk $\gamma_{xy}$ between every distinct ordered pair, write $\eta$ for the directed-edge congestion in (3.2). Let $h$ be the minimum of $Q(S\times S^{\mathrm c})/\pi(S)$ over nonempty $S$ with $\pi(S)\leq\tfrac12$. Then
--
--   $$
--   h\geq\frac{1}{2\eta}.
--   $$
--
--   This converts a bound on chosen walk congestion into a lower bound on the chain's bottleneck constant.
--
--   **Formalization Note** The two-state hypothesis gives meaning to the second eigenvalue used by the surrounding proposition and ensures a nonempty positive-flow edge family. Equal-endpoint walks do not enter $\eta$.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 54, §3B, proof of Proposition 7; https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_lower
import Definitions.Def_DiaconisStroock_CanonPaths_Eta

namespace DiaconisStroock.CanonPaths

open MarkovMixing

/-- Canonical-path congestion bounds the bottleneck constant from below
(§3B, proof of Proposition 7, p. 54). -/
theorem bottleneckStar_ge {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (Γ : V → V → List V)
    (hΓ : IsWalkSystem P π Γ) :
    1 / (2 * eta P π Γ) ≤ bottleneckStar P π := by sorry

end DiaconisStroock.CanonPaths
