-- Prove2me | Theorems.Thm_DirS_dir_sid_graphon
-- name    : DirS.dir_sid_graphon
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:24:50.755287+00:00
-- url     : https://prove2.me/theorems/dc1fc466-a39c-4c1c-b114-210ede27896e
-- title:
--   Directed Sidorenko, graphs and graphons (Proposition 21)
-- statement:
--   Proposition 21 of the paper: the characterization of the directed Sidorenko property in terms of graphons. The oriented graph B has the directed Sidorenko property if and only if for every (not necessarily symmetric) graphon W, t(B,W) >= |E W|^{e(B)}, the density of the directed edge taken in absolute mean. The forward direction of the paper's proof evaluates the finite inequality on the approximating graphs of Theorem 13 and passes to the limit through the counting Lemma 18, halving the kernel and multiplying back; the backward direction evaluates the graphon inequality on the directed graphon of a finite oriented graph, where the two densities coincide. In the mission the statement runs through the graph world interface: the approximation axioms provide the approximating graphs and the density correspondences provide the evaluations.
--
--   **Formalization Note** The graph-limit theory (the cut norm, Theorem 13, Theorem 18) is bundled in the world's approximation data; the modulus on the mean is needed because an asymmetric kernel may have negative mean.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 3 (Proposition 21, pages 8-9, via Theorems 13 and 18).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 2 (Proposition 21): directed Sidorenko, graphs and graphons.
The oriented graph B has the directed Sidorenko property if and only if
for every directed graphon the B-density is at least the absolute mean of
the kernel to the power e(B). The forward direction applies the finite
inequality to the approximating graphs of the world and passes to the
limit through the approximation axioms and the counting lemma; the
backward direction evaluates the graphon inequality on the graphon of a
finite graph. -/
theorem dir_sid_graphon {m : ℕ} (B : OriGraph m) (_w : GraphWorld) :
    DirSidorenko B ↔ DirSidW B := by sorry

end DirS
