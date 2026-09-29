-- Prove2me | Theorems.Thm_Devaney_itinerary_homeomorph
-- name    : Devaney.itinerary_homeomorph
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:51:51.306502+00:00
-- url     : https://prove2.me/theorems/4ef11e53-9e4b-4425-9772-6d5842b6a952
-- title:
--   Theorem 7.2 — the itinerary map $S : \Lambda \to \Sigma_2$ is a homeomorphism
-- statement:
--   Let $\mu > 2 + \sqrt 5$. The itinerary map
--
--   $$S : \Lambda \to \Sigma_2, \qquad S(x)_j = \begin{cases} 0 & F_\mu^{\,j}(x) \in I_0,\\ 1 & F_\mu^{\,j}(x) \in I_1,\end{cases}$$
--
--   is a homeomorphism from the invariant Cantor set $\Lambda$ (with the topology inherited from $\mathbb{R}$) onto the sequence space $\Sigma_2$.
--
--   Injectivity comes from total disconnectedness of $\Lambda$, surjectivity from the nested-interval construction $I_{s_0\dots s_n} = I_{s_0} \cap F_\mu^{-1}(I_{s_1}) \cap \dots \cap F_\mu^{-n}(I_{s_n})$, and continuity from Proposition 6.3. As sets, $\Lambda$ and $\Sigma_2$ are the same object.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, pp. 44–46, Theorem 7.2 (itinerary: Definition 7.1, p. 44)

import Mathlib
import Definitions.Def_Devaney_chaos
import Definitions.Def_Devaney_conjugacy
import Definitions.Def_Devaney_sigma2
import Definitions.Def_Devaney_quadratic

namespace Devaney
theorem itinerary_homeomorph (μ : ℝ) (hμ : 2 + Real.sqrt 5 < μ) :
    ∃ h : (Lambda μ) ≃ₜ Sigma2, ∀ x : Lambda μ, h x = itinerary μ x.1 := by sorry
end Devaney
