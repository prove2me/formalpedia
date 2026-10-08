-- Prove2me | Theorems.Thm_DGPNash_NashMap_lemma_3_4
-- name    : DGPNash.NashMap.lemma_3_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T10:04:56.358973+00:00
-- url     : https://prove2.me/theorems/1c92c88e-7aa7-4c62-b8ce-44176c446d72
-- title:
--   Lemma 3.4 — Nash's map is Lipschitz
-- statement:
--   In a game of $r\ge2$ players with $n>0$ strategies each and nonnegative payoff entries, let $U_{\max}$ be the largest entry in the payoff tables. If mixed profiles $x,x'$ differ by at most $\delta\ge0$ in every coordinate, Nash's map satisfies
--
--   $$\|f(x)-f(x')\|_\infty\le[1+2U_{\max}rn(n+1)]\delta.$$
--
--   The explicit constant is the continuity bound used for the paper's grid approximation. **Formalization Note** The infinity norm is expressed as a bound for every player-strategy coordinate; $U_{\max}$ is computed from the game rather than supplied as an arbitrary upper bound.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 205, Lemma 3.4; https://doi.org/10.1137/070699652

import Definitions.Def_DGPNash_NashMap_nashMap

namespace DGPNash.NashMap

/-- Lemma 3.4, p. 205: Nash's map has the paper's explicit Lipschitz constant. -/
theorem lemma_3_4 {r n : ℕ} (hr : 2 ≤ r) (hn : 0 < n)
    (u : Fin r → (Fin r → Fin n) → ℝ) (hu : ∀ p s, 0 ≤ u p s)
    (x x' : Fin r → Fin n → ℝ)
    (hx : AGT.IsMixedProfile x) (hx' : AGT.IsMixedProfile x')
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hclose : ∀ p j, |x p j - x' p j| ≤ δ) :
    ∀ p j, |nashMap u x p j - nashMap u x' p j| ≤
      (1 + 2 * maxPayoff u * (r : ℝ) * (n : ℝ) * ((n : ℝ) + 1)) * δ := by sorry

end DGPNash.NashMap
