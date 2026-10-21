-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm2_point2
-- name    : DealerDissem.RankFree.proof_thm2_point2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:25.990329+00:00
-- url     : https://prove2.me/theorems/6182be51-4767-430f-95b5-c58b1f21d490
-- title:
--   Proof of Theorem 2, point 2, pp. 42–43 — no offer yields an expected transaction payoff above $r\Omega(y)$
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Let the next dealer follow the Theorem 2 acceptance rule: a dealer of type $\omega$ accepts $(p,v)$ iff $(\rho-p)v-rz+r\Omega(z)\ge0$ with $z=\max(pv-\omega,0)$, and let $\Phi(p,v)$ be the probability of acceptance under $G$. Then for every $y\ge0$ and every offer $p,v\ge0$,
--   $$q\,\Phi(p,v)\bigl[r\min(pv,y)-(\rho-p)v\bigr]\le r\,\Omega(y).$$
--
--   The left side is the expected transaction payoff of a dealer with financing needs $y$ who makes the offer $(p,v)$. The bound is the upper half of the optimality argument of Theorem 2.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46). The bound is stated for every offer with $p,v\ge0$, not only those with $v$ below a received volume; the paper's argument does not use that constraint. The first sentence of point 2 says "not greater than $\Omega(y)$"; the bound proved, and stated here, is $r\Omega(y)$.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), pp. 42–43 (PDF 44–45), proof of Theorem 2, point 2, (49)–(52)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 2, point 2, pp. 42–43: when the next dealer follows the Theorem 2
acceptance rule, no offer `(p, v)` yields an expected transaction payoff above `r Ω(y)`. -/
theorem proof_thm2_point2 (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω)
    (y : ℝ) (hy : 0 ≤ y) (p v : ℝ) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    P.q * accProb μ (thmAccept P Ω) p v * (P.r * min (p * v) y - (P.ρ - p) * v)
      ≤ P.r * Ω y := by sorry

end DealerDissem.RankFree
