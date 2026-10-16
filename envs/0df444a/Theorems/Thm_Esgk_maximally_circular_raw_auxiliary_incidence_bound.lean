-- Prove2me | Theorems.Thm_Esgk_maximally_circular_raw_auxiliary_incidence_bound
-- name    : Esgk.maximally_circular_raw_auxiliary_incidence_bound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-16T05:09:27.340436+00:00
-- url     : https://prove2.me/theorems/74601ba8-725e-4c44-b78b-da295e6e93c8
-- title:
--   Auxiliary incidence bound at every scale
-- statement:
--   There is an absolute positive integer $K$ with the following property.
--
--   Let $G$ be an irreducible and absolutely irreducible real plane polynomial of degree $d$, with real zero set $C$. Assume that $G$ is not a circle factor and is maximally circular: its local order at each of the two complex circular points at infinity is $d/2$. Let $S\subset C$ be finite and put $N=|S|$.
--
--   Take any incidence configuration whose two carrier sets are both $C$, each represented by an irreducible real polynomial of degree at most $d$. Its finite point sets $P_1,P_2$ are subsets of $C$ and form a disjoint split $S=P_1\sqcup P_2$. The carrier is neither a line nor a circle: in particular neither copy is a vertical line, the pair is neither parallel lines, perpendicular lines, nor concentric circles, and the conditional restrictions on line or circle carriers hold automatically. Assume
--
--   $$
--   0<|P_1||P_2|,\qquad |P_1|\le2|P_2|,\qquad |P_2|\le2|P_1|.
--   $$
--
--   Let $I$ count ordered pairs of a label $(a,b)\in P_1\times P_1$ and a target $(p,q)\in P_2\times P_2$ satisfying $\|a-p\|^2=\|b-q\|^2$. For every integer $j\ge24d$,
--
--   $$
--   I\le K\left(\frac{dN^3}{\sqrt j}+d^2jN^2+N^2+d^4j^2+d^3N^2\right).
--   $$
--
--   The constant $K$ is independent of the polynomial, sample, incidence configuration, and scale. The balanced cell-cover construction supplies such a configuration for every sample with $N\ge2$.

import Definitions.Def_Esgk_MaximallyCircularQuarticFromIncidence

open Esgk

theorem Esgk.maximally_circular_raw_auxiliary_incidence_bound :
    MaximallyCircularRawAuxiliaryIncidenceStatement := by sorry
