-- Prove2me | Theorems.Thm_Esgk_maximally_circular_quartic_distance_bound
-- name    : Esgk.maximally_circular_quartic_distance_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-16T05:09:45.22198+00:00
-- url     : https://prove2.me/theorems/2b0f331a-d4f9-4295-ba35-f6d708f72d7c
-- title:
--   Quartic distinct-distance bound on a maximally circular curve
-- statement:
--   There are absolute positive integers $T,C_0$ with the following property.
--
--   Let $G$ be an irreducible and absolutely irreducible real plane polynomial of degree $d$, with real zero set $C$. Assume that $G$ is not a circle factor and is maximally circular: its local order at each of the two complex circular points at infinity is $d/2$. For a finite sample $S\subset C$, write $N=|S|$ and
--
--   $$
--   D(S)=\bigl|\{\|x-y\|:x,y\in S,\ x\ne y\}\bigr|.
--   $$
--
--   Then
--
--   $$
--   Td^5\le N^2\quad\Longrightarrow\quad N^4\le C_0d^4D(S)^3.
--   $$
--
--   Both constants are independent of the curve and sample. The conclusion gives the lower bound $D(S)\ge C_0^{-1/3}d^{-4/3}N^{4/3}$ under the stated threshold.

import Definitions.Def_Esgk_MaximallyCircularQuarticBootstrap

open Esgk

theorem Esgk.maximally_circular_quartic_distance_bound :
    MaximallyCircularQuarticDistinctDistancesStatement := by sorry
