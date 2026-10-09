-- Prove2me | Theorems.Thm_CostSharingPNE_Potential_localPotential_satisfies_83
-- name    : CostSharingPNE.Potential.localPotential_satisfies_83
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:30:17.729891+00:00
-- url     : https://prove2.me/theorems/e6c49414-0059-4401-a06b-7f02bace8f60
-- title:
--   Theorem 3 proof steps (a)–(b), pp. 58–59 — the closed form satisfies (83)
-- statement:
--   Let $\omega=(\lambda,\Sigma)$ be a weight system and let $W''$ be a ground welfare function. Define the vector-valued local potential by the closed form (85), so component $c$ evaluates $W''$ on the part of the coalition at or after the reverse-indexed priority block. If player $i$ lies in block $k$, every component before the fixed component $K-k+1$ is unchanged when $i$ is removed, and
--
--   $$f^{W''}_{\mathrm{GWMC}}[\omega](i,S)=\lambda_i\bigl(\phi(S)_{K-k+1}-\phi(S\setminus\{i\})_{K-k+1}\bigr),\qquad i\in S.$$
--
--   This is the local potential identity used to turn the marginal-contribution rule into the game-level potential of Theorem 3.
--
--   **Formalization Note** Blocks and components are zero-based in Lean; the player's component is the reversal of its block index. The earlier-component condition is explicit, and no nonzero change at the player's component is required. The theorem does not assume $W''(\varnothing)=0$.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Theorem 3 proof steps (a)–(b), pp. 58–59; (85), p. 58

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

namespace CostSharingPNE.Potential

/-- Appendix C, Theorem 3 proof steps (a) and (b), with the fixed player index. -/
theorem localPotential_satisfies_83 {n : ℕ} (ω : CostSharingPNE.Char.WeightSystem n) (W'' : CostSharingPNE.Char.Welfare n) :
    ∀ S : Finset (Fin n), ∀ i ∈ S,
      (∀ c, c < (ω.block i).rev →
        localPotential ω W'' S c = localPotential ω W'' (S.erase i) c) ∧
      CostSharingPNE.Char.gwmc ω W'' i S = ω.lam i *
        (localPotential ω W'' S (ω.block i).rev -
          localPotential ω W'' (S.erase i) (ω.block i).rev) := by sorry

end CostSharingPNE.Potential
