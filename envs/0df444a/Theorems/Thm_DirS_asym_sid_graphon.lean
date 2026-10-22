-- Prove2me | Theorems.Thm_DirS_asym_sid_graphon
-- name    : DirS.asym_sid_graphon
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:25:17.152051+00:00
-- url     : https://prove2.me/theorems/638b831e-4568-44e4-b74e-0cd87efb0ac3
-- title:
--   Asymmetric Sidorenko, graphs and graphons (Proposition 22)
-- statement:
--   Proposition 22 of the paper: the bipartite counterpart of Proposition 21. The bipartite graph A has the asymmetric Sidorenko property if and only if for every graphon W, t_bip(A,W) >= |E W|^{e(A)}. The proof is the same approximation argument run on bipartite graphs: the bipartite graphon of a finite bipartite graph witnesses the backward direction, and the approximation scheme of Theorem 13 with the counting Lemma 18 carries the forward direction. In the mission the statement runs through the bipartite side of the graph world interface, consuming the bipartite approximation axioms.
--
--   **Formalization Note** The asymmetric Sidorenko property quantifies only over bipartite graphs H with their two parts; the graphon inequality quantifies over all kernels, symmetric or not.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 3 (Proposition 22, page 9, via Theorems 13 and 18).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 3 (Proposition 22): asymmetric Sidorenko, graphs and
graphons. The bipartite graph A has the asymmetric Sidorenko property if
and only if for every directed graphon the bipartite A-density is at
least the absolute mean of the kernel to the power e(A). The proof is the
bipartite counterpart of Proposition 21, running through the bipartite
graphon of a finite bipartite graph and the bipartite approximation
scheme of the world. -/
theorem asym_sid_graphon {mA nA : ℕ} (A : BipGraph mA nA) (_w : GraphWorld) :
    AsymSidorenko A ↔ AsymSidW A := by sorry

end DirS
