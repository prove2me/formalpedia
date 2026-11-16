-- Prove2me | Theorems.Thm_AgreementTop736_Exact_Supplement_theorem_18
-- name    : AgreementTop736.Exact.Supplement.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:44:12.512717+00:00
-- url     : https://prove2.me/theorems/c5550197-594d-4186-bc5f-1d290d170958
-- title:
--   Theorem 18 — exact agreement under a local distance guarantee
-- statement:
--   Let $P_0,\ldots,P_k$ be a finite coherent layered poset of subsets of a finite ground set $X$, with layer cardinalities $q_j$, positive subface counts $d_{i,j}$, and an arbitrary top probability law $\mu$. Fix $h<k$, $0<\kappa\le1$, and a rank $r\in R(\kappa)$ with $\xi_{k,r}>0$. Here $r\in R(\kappa)$ means that any error set occupying at least a $\kappa$ fraction of an $r$-face in a supported top face is hit by a uniform $h$-face with probability at least $1/2$. The detection parameter $\xi_{k,r}$ is defined by (13)–(14).
--
--   Let $F_K:K\to\Sigma$ be local assignments in any finite alphabet. For each $s\in\{h,r\}$, suppose there exists a global assignment $g_s$ with
--   $$\Pr_{K\sim\mu,\ S\sim D_s(\cdot\mid K)}[F_K|_S\ne g_s|_S]\le A_s\tau_s,$$
--   where $D_s$ samples a uniform $s$-face inside $K$, and $\tau_s$ is the exact $(k,s)$-test rejection probability. The two witnesses may differ. Suppose distinct restrictions of actual local assignments from any supported parents to any positive-mass $r$-face $R$ differ in at least $\theta_r|R|$ coordinates, with $\theta_r\ge2\kappa$.
--
--   There is a globally optimal assignment $g$ for which
--   $$\Delta(F)=\Pr_K[F_K\ne g|_K]\le\frac{4A_hA_r}{\xi_{k,r}}\tau_h.$$
--   The constants $A_s$ are real inputs to the deviation premises. There is no additional sign condition on them, no ordering condition between $h$ and $r$, and no spectral hypothesis. Equality $\theta_r=2\kappa$ is included.
--
--   This companion theorem transfers the two per-layer deviation estimates to an exact global agreement bound on the general coherent layered poset.
--
--   Differences from the source:
--   - encoding: finite coherent layered poset and its induced probability laws → finite face families with the coherence denominator cleared, and the published scheme instantiated at each tested rank with the same top law; reason: positive subface counts make the cleared identity equivalent and yield exactly the uniform subface, marginal and independent conditional-parent laws
--   - encoding: ξ_{k,r} detects every nonempty error set → the finite minimum of singleton inclusion probabilities over supported top-element pairs; reason: equation (14) explicitly identifies the two minima; zero-mass faces are omitted throughout Section 2
--   - encoding: local assignments on faces, distinct restrictions on r-faces and separate global witnesses g_s → total extensions with all comparisons restricted to their faces, supported parents and faces, and an existential deviation witness at each of h and r; reason: this represents every source instance, permits equal restrictions, and does not identify the two witnesses
--   - encoding: Δ is the minimum global disagreement and Δ≤4 A_h A_r τ_h/ξ_{k,r} → a global minimizer is exhibited and its disagreement obeys the identical bound; reason: the alphabet and ground set are finite and F_∅ supplies a global candidate, so the minimum is attained
-- source:
--   Tali Kaufman, Huy Tuan Pham, Exact Agreement Expansion up to the Top via Non-polarity, STOC 2027 submission #736 (October 2026), p.16, Theorem 18. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/736.pdf

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Supplement_Transfer

namespace AgreementTop736.Exact.Supplement

/-- Theorem 18, p.16, (15)–(16). The two deviation witnesses may differ.
There is no ordering premise between h and r, no spectral premise, and no added
sign premise on A_h or A_r. The conclusion includes attainment of Δ. -/
theorem theorem_18 {V : Type*} [Fintype V] [DecidableEq V]
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : LayeredPoset V) (hP : P.IsCoherent)
    (h r : ℕ) (hh : h < P.k) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hr : P.IsHittingRank h r κ) (hξ : 0 < P.detectionMinimum r)
    (F : Finset V → V → α) (A : ℕ → ℝ) (θr : ℝ)
    (hdevh : P.HasDeviationBound h F (A h)) (hdevr : P.HasDeviationBound r F (A r))
    (hθ : 2 * κ ≤ θr) (hdist : P.HasRestrictedDistance r F θr) :
    ∃ g : V → α,
      P.optimalDistance F = (P.scheme h).disagreementProb F g ∧
      (P.scheme h).disagreementProb F g ≤
        (4 * A h * A r / P.detectionMinimum r) * (P.scheme h).rejectionProb F := by sorry

end AgreementTop736.Exact.Supplement
