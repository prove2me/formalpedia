-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm2_point3
-- name    : DealerDissem.RankFree.proof_thm2_point3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:31.920977+00:00
-- url     : https://prove2.me/theorems/c3655f9d-f9a8-4a6d-8ab8-63227621313b
-- title:
--   Proof of Theorem 2, point 3, pp. 43–44 — $(P(y),V(y))$ is accepted exactly by types $\omega\ge T(y)$ and achieves $r\Omega(y)$
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Let $T$ be a selection of the targeted values and $(P(y),V(y))$ the offer of (14): $P(y)V(y)=y$ and $\rho V(y)=(1+r)y-r[T(y)+\Omega(y-T(y))]$. Let $\Phi$ be the acceptance probability under the Theorem 2 acceptance rule. Then for every $y>0$:
--
--   1. a dealer of type $\omega$ accepts $(P(y),V(y))$ under the Theorem 2 rule if and only if $\omega\ge T(y)$;
--   2. the expected transaction payoff of the offer is exactly
--   $$q\,\Phi(P(y),V(y))\bigl[r\min(P(y)V(y),y)-(\rho-P(y))V(y)\bigr]=r\,\Omega(y).$$
--
--   Together with point 2 this shows the offer $(P(y),V(y))$ is optimal.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46). $H$ is the closed tail $\Pr(\tilde\omega\ge\omega)$, so the acceptance probability is $H(T(y))$ also at atoms of $G$. The equivalence in 1 holds for every real $\omega$.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), pp. 43–44 (PDF 45–46), proof of Theorem 2, point 3

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 2, point 3, pp. 43–44: for `y > 0`, the offer `(P(y), V(y))` is accepted
exactly by the types `ω ≥ T(y)`, and its expected transaction payoff is `r Ω(y)`. -/
theorem proof_thm2_point3 (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) (T : ℝ → ℝ) (hT : IsSelection P μ Ω T) (y : ℝ) (hy : 0 < y) :
    (∀ ω, thmAccept P Ω (offerP P Ω T y) (offerV P Ω T y) ω ↔ T y ≤ ω) ∧
    P.q * accProb μ (thmAccept P Ω) (offerP P Ω T y) (offerV P Ω T y) *
        (P.r * min (offerP P Ω T y * offerV P Ω T y) y - (P.ρ - offerP P Ω T y) * offerV P Ω T y)
      = P.r * Ω y := by sorry

end DealerDissem.RankFree
