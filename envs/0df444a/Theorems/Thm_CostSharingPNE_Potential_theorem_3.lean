-- Prove2me | Theorems.Thm_CostSharingPNE_Potential_theorem_3
-- name    : CostSharingPNE.Potential.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:08.533306+00:00
-- url     : https://prove2.me/theorems/ba911a0f-49ee-412a-9fd3-f27eeedfa193
-- title:
--   Theorem 3, p. 58 — generalized weighted Shapley rules yield a vector potential
-- statement:
--   Consider a finite welfare sharing game with a weight system $\omega=(\lambda,\Sigma)$. At each resource $r$, suppose its rule $f^r$ equals both the generalized weighted Shapley value for a ground welfare $W'_r$ and the generalized weighted marginal contribution rule for a ground welfare $W''_r$. For every nonempty coalition $T$, suppose their Möbius coefficients satisfy (12):
--
--   $$q_T^{W'_r}=\Bigl(\sum_{j\in\bar T}\lambda_j\Bigr)q_T^{W''_r}.$$
--
--   Then the game has a generalized weighted potential with player weights $\lambda$. It is separable across resources, and its local potential has the closed form
--
--   $$\Phi(a)=\sum_{r\in R}\phi_r(\{a\}_r),\qquad (\phi_r(S))_k=W''_r(\bar S_{K-k+1})\quad(1\le k\le K).$$
--
--   This supplies an explicit vector potential for the distribution rules characterized elsewhere in the paper.
--
--   **Formalization Note** The vector component for player $i$ is fixed by its priority block, with earlier components unchanged. This corrects the printed “first nonzero term” reading of Definition 1. The recursive formula (84) is omitted because it disagrees with (85) for two or more blocks; a two-player counterexample is recorded in the moderation notes. Action sets are unrestricted because the theorem asserts a potential identity, not an equilibrium-existence conclusion. Equality of distribution rules is checked on $i\in S$, the domain on which they are used.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Theorem 3 and (84)–(85), p. 58; (12), p. 11

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

namespace CostSharingPNE.Potential

/-- Appendix C, Theorem 3, using its closed form (85) and fixed per-player index. -/
theorem theorem_3
    (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (ω : CostSharingPNE.Char.WeightSystem n)
    (A : Fin n → Finset (Finset (Fin m)))
    (F : Fin m → CostSharingPNE.Char.Rule n) (W' W'' : Fin m → CostSharingPNE.Char.Welfare n)
    (h12 : ∀ r, ∀ T : Finset (Fin n), T.Nonempty →
      CostSharingPNE.Char.mobius (W' r) T =
        (∑ j ∈ CostSharingPNE.Char.tbar ω T, ω.lam j) * CostSharingPNE.Char.mobius (W'' r) T)
    (hF : ∀ r S, ∀ i ∈ S,
      F r i S = CostSharingPNE.Char.gwsv ω (W' r) i S ∧
      F r i S = CostSharingPNE.Char.gwmc ω (W'' r) i S) :
    IsGenWeightedPotential A (fun i a => utility F a i)
      (fun a => ∑ r, localPotential ω (W'' r) (CostSharingPNE.Char.players a r)) ω.lam := by sorry

end CostSharingPNE.Potential
