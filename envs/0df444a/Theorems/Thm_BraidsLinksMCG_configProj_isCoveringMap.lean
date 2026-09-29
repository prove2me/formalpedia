-- Prove2me | Theorems.Thm_BraidsLinksMCG_configProj_isCoveringMap
-- name    : BraidsLinksMCG.configProj_isCoveringMap
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:43:48.509804+00:00
-- url     : https://prove2.me/theorems/6610677d-27e2-4db1-869c-90bfe99f6d05
-- title:
--   Ordered over unordered configurations is a covering map
-- statement:
--   The projection from the ordered to the unordered configuration space of $n$ points in the plane,
--
--   $$F_{0,n}E^{2} \longrightarrow B_{0,n}E^{2},$$
--
--   is a covering map. It is the quotient by the free action of the symmetric group $\mathfrak{S}_n$ permuting the coordinates of a configuration.
--
--   This is the first conjunct of `BraidsLinksMCG.prop_1_1_covering`, separated out because it is purely a statement about the map of spaces, while the other conjunct is about the induced homomorphism on fundamental groups. The two are used at different points and by different arguments.
--
--   The proof is the standard one for a quotient by a properly discontinuous free action. The action of $\mathfrak{S}_n$ on ordered configurations is free precisely because the coordinates of a configuration are distinct: a nontrivial permutation moves at least one coordinate to a different value. Local triviality then follows by separating the $n$ points with disjoint open balls, which is possible in a Hausdorff space; the preimage of the resulting neighbourhood in the unordered space is a disjoint union of $n!$ homeomorphic sheets, one for each labelling. Mathlib's `IsQuotientCoveringMap` machinery packages exactly this, given the free action and the local disjointness.
--
--   It is this covering that produces the underlying-permutation homomorphism by monodromy: lifting a loop of unordered configurations to a path of ordered ones, the endpoint differs from the start by the permutation the braid induces on its strands.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Proposition 1.1; Fadell and Neuwirth, Configuration spaces.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem configProj_isCoveringMap (n : ℕ) :
    IsCoveringMap (configProj n) := by sorry

end BraidsLinksMCG
