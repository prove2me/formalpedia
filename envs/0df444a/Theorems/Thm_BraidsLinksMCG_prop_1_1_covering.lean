-- Prove2me | Theorems.Thm_BraidsLinksMCG_prop_1_1_covering
-- name    : BraidsLinksMCG.prop_1_1_covering
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:58:47.583443+00:00
-- url     : https://prove2.me/theorems/9e721edf-30d3-4b97-9ced-07808f464ddc
-- title:
--   Proposition 1.1: $F_{0,n}E^2 \to B_{0,n}E^2$ is a regular covering with group $\Sigma_n$
-- statement:
--   **Proposition 1.1 (for $M = E^2$).** The natural projection $p : F_{0,n}E^2 \to B_{0,n}E^2$ from
--   ordered to unordered configurations of $n$ points of the plane is a covering space projection,
--   and the quotient of $\pi_1 B_{0,n}E^2$ by the image of $\pi_1 F_{0,n}E^2$ is the symmetric group
--   $\Sigma_n$ (equation (1-3)).
--
--   The second half is formalized as the exactness of
--   $$\pi_1 F_{0,n}E^2 \xrightarrow{\;p_*\;} \pi_1 B_{0,n}E^2 \xrightarrow{\;\nu\;} \Sigma_n \to 1 ,$$
--   that is: there is a surjective homomorphism $\nu$ from the braid group onto the symmetric group
--   whose kernel is exactly the image of the pure braid group under the map induced by $p$. The
--   homomorphism $\nu$ records which permutation of the $n$ points a braid induces.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 11, Proposition 1.1 (including equation (1-3))

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem prop_1_1_covering (n : ℕ) :
    IsCoveringMap (configProj n) ∧
      ∃ nu : GeomBraidGroup n →* Equiv.Perm (Fin n),
        Function.Surjective nu ∧
        nu.ker = (FundamentalGroup.map (configProj n) (baseOrdered n)).range := by sorry

end BraidsLinksMCG
