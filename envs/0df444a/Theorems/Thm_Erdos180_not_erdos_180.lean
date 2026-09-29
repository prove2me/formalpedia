-- Prove2me | Theorems.Thm_Erdos180_not_erdos_180
-- name    : Erdos180.not_erdos_180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:21:32.232815+00:00
-- url     : https://prove2.me/theorems/1d0155e3-12c8-4d87-86d4-1b3e462b9f9a
-- title:
--   Refutation of the Erdős-Simonovits compactness conjecture (Erdős problem #180)
-- statement:
--   The compactness conjecture is false: it is **not** the case that for every finite nonempty
--   family $\mathcal{F}$ of graphs, all of whose members contain a cycle, there exist
--   $F \in \mathcal{F}$ and $C > 0$ with
--
--   $$\mathrm{ex}(n, F) \;\le\; C\, \mathrm{ex}(n, \mathcal{F}) \qquad
--   \text{for all sufficiently large } n.$$
--
--   Erdős and Simonovits conjectured that the extremal number of a finite family is, up to a
--   constant factor, the extremal number of one of its members. The original formulation admits
--   simple counterexamples such as the folklore family $\{K_{1,2}, 2K_2\}$, which is why the
--   corrected form restricts to families whose members all contain cycles. The family
--   $\mathcal{F} = \{C_4, C_6\} \cup \mathcal{J} \cup \mathcal{K}$ of Definition 2.5 refutes even
--   that form, and does so with every member connected and bipartite.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L8967-L8970

import Definitions.Def_erdos180_core4
import Init.Prelude

open Erdos180
open SimpleGraph

theorem Erdos180.not_erdos_180 :
    ¬ CompactnessConjectureStatement := by sorry
