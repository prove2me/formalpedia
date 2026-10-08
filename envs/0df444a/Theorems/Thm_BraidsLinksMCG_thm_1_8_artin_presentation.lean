-- Prove2me | Theorems.Thm_BraidsLinksMCG_thm_1_8_artin_presentation
-- name    : BraidsLinksMCG.thm_1_8_artin_presentation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:58:09.814638+00:00
-- url     : https://prove2.me/theorems/75ea0df7-a7ac-46e0-9110-b672782e1166
-- title:
--   Theorem 1.8 (Artin, 1925): $B_n \cong \pi_1 B_{0,n}E^2$
-- statement:
--   **Theorem 1.8 (Artin, 1925).** The group $\pi_1 B_{0,n}E^2$ admits a presentation with generators
--   $\sigma_1, \dots, \sigma_{n-1}$ and defining relations
--
--   $$\sigma_i\sigma_j = \sigma_j\sigma_i \quad (|i-j| \ge 2,\ 1 \le i, j \le n-1), \qquad
--     \sigma_i\sigma_{i+1}\sigma_i = \sigma_{i+1}\sigma_i\sigma_{i+1} \quad (1 \le i \le n-2).$$
--
--   Equivalently, the abstract group $B_n$ defined by that presentation is isomorphic to the
--   fundamental group of the space of unordered $n$-point subsets of the plane, i.e. to the group of
--   braids on $n$ strands. The relations are easily seen to hold between the elementary braids
--   $\sigma_i$; the content of the theorem is that they are *defining*, so that every relation
--   between braids is a consequence of them.
--
--   The formal statement asserts the existence of a group isomorphism between the presented group
--   and $\pi_1 B_{0,n}E^2$ at the base configuration $(1,2,\dots,n)$. It does not additionally
--   require the isomorphism to carry $\sigma_i$ to the specific geometric generator of Figure 2,
--   since those loops are not part of the formal development.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 18, Theorem 1.8 [Artin, 1925]; relations (1-1), (1-2) on p. 11

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem thm_1_8_artin_presentation (n : ℕ) :
    Nonempty (ArtinBraidGroup n ≃* GeomBraidGroup n) := by sorry

end BraidsLinksMCG
