-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm2_point1
-- name    : DealerDissem.RankFree.proof_thm2_point1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:18.521718+00:00
-- url     : https://prove2.me/theorems/5fbe75a7-3a6a-40ca-9798-00855b0edc8c
-- title:
--   Proof of Theorem 2, point 1, p. 42 — the offer $(P(y),V(y))$ is feasible: $0\le V(y)\le v-\omega/\rho$
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Let $T$ be a selection of the targeted values, $T(y)\in\mathcal T(y)$ for every $y\ge0$, and let
--   $$\rho V(y)=(1+r)y-r\bigl[T(y)+\Omega(y-T(y))\bigr]$$
--   be the volume of the offer of (14). Let a dealer of type $\omega\ge0$ receive an offer $(p,v)$ with $p,v\ge0$, have financing needs $y=\max(pv-\omega,0)>0$, and accept it under the Theorem 2 rule, i.e. $\pi^*(p,v,y)=(\rho-p)v-ry+r\Omega(y)\ge0$. Then
--   $$0\le V(y)\le v-\frac{\omega}{\rho}.$$
--
--   So the new offer is feasible ($V(y)\le v$), and the dealer keeps enough units to serve her own customers.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46). The case $y=0$, where $V(0)=0$ and $v-\omega/\rho$ may be negative, is excluded, as in the theorem's own "For $y>0$"; in the paper's notation of the proof, $v-\omega/\rho=v_0-v^C_1$.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 42 (PDF 44), proof of Theorem 2, point 1, (48)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 2, point 1, p. 42: a dealer who accepts `(p, v)` under the Theorem 2
rule and has financing needs `y > 0` makes an offer with `0 ≤ V(y) ≤ v − ω/ρ`. -/
theorem proof_thm2_point1 (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) (T : ℝ → ℝ) (hT : IsSelection P μ Ω T)
    (p v ω : ℝ) (hp : 0 ≤ p) (hv : 0 ≤ v) (hω : 0 ≤ ω) (hacc : thmAccept P Ω p v ω)
    (hy : 0 < finNeeds p v ω) :
    0 ≤ offerV P Ω T (finNeeds p v ω) ∧ offerV P Ω T (finNeeds p v ω) ≤ v - ω / P.ρ := by sorry

end DealerDissem.RankFree
