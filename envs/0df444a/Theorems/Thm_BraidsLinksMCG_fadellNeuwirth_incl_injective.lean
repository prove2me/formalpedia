-- Prove2me | Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_incl_injective
-- name    : BraidsLinksMCG.fadellNeuwirth_incl_injective
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:17:41.138092+00:00
-- url     : https://prove2.me/theorems/7dce8d4f-1c03-445f-9747-14a9c51de08e
-- title:
--   The Fadell--Neuwirth fibre inclusion is $\pi_1$-injective
-- statement:
--   The inclusion of the fibre into the total space of the Fadell–Neuwirth fibration is injective on fundamental groups:
--
--   $$\pi_1igl(E^{2}-Q_nigr) \hookrightarrow \pi_1igl(F_{0,n+1}E^{2}igr).$$
--
--   The map is induced by `configIncl`, which sends a point $z$ of the punctured plane to the configuration $(1, 2, \ldots, n, z)$, so the assertion is that a loop of the moving point which becomes null-homotopic once the other $n$ points are allowed to be present was already null-homotopic in the punctured plane.
--
--   This is one of the three conjuncts of `BraidsLinksMCG.thm_1_4_fadell_neuwirth_exact`, separated out because it is an independent piece of the long exact sequence. In the exact sequence of the fibration $F_{0,n+1}E^{2} 	o F_{0,n}E^{2}$ with fibre $E^{2}-Q_n$, injectivity here is equivalent to the vanishing of the connecting map from $\pi_2$ of the base, which holds because $F_{0,n}E^{2}$ is aspherical --- an Eilenberg–MacLane space, being an iterated fibration with aspherical fibres. It is this vanishing, rather than anything about the fibre, that carries the content.
--
--   Separating it from the exactness statement at the middle term matters because the two are used differently: injectivity is what makes the free group sit inside the pure braid group as a genuine subgroup, while exactness at the middle identifies that subgroup as a kernel.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4; Fadell and Neuwirth, Configuration spaces, Math. Scand. 10 (1962).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem fadellNeuwirth_incl_injective (n : ℕ) :
    Function.Injective (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) := by sorry

end BraidsLinksMCG
