-- Prove2me | Theorems.Thm_Erdos180_jQuotient_mem_proposedFamily
-- name    : Erdos180.jQuotient_mem_proposedFamily
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:01:31.637625+00:00
-- url     : https://prove2.me/theorems/81b3575a-bd63-4112-b09f-33a9dd4c259c
-- title:
--   Admissible quotients of $J_0$ belong to $\mathcal{F}$
-- statement:
--   For every admissible identification $f$ of the template $J_0$, the encoded quotient
--   $J_0/\!\approx$ is a member of $\mathcal{F}$, i.e. $\mathcal{J} \subseteq \mathcal{F}$
--   (Definitions 2.3 and 2.5).
--
--   Excluding $\mathcal{J}$ is what bounds the number of possible base triples in Proposition 3.4:
--   if two distinct vertices of the third-base set $A_{yz}$ were related, their witnessing copies of
--   $S_2$ together with their common neighbour would produce a member of $\mathcal{J}$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L708-L711

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Data.Fintype.Sum

open Erdos180
open Finset SimpleGraph

theorem Erdos180.jQuotient_mem_proposedFamily
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily := by sorry
