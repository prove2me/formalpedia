-- Prove2me | Theorems.Thm_DirS_bip_dir_density
-- name    : DirS.bip_dir_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:24:04.375879+00:00
-- url     : https://prove2.me/theorems/1a53f039-7fc4-46ec-9176-10ce97a1e02a
-- title:
--   Directed and bipartite densities agree on the orientation (Observation 16)
-- statement:
--   Observation 16 of the paper: let the oriented graph B be obtained from the undirected bipartite graph H by directing every edge from the first part to the second. Then for every graphon W (the paper's graphons are not necessarily symmetric), the directed homomorphism density t(B,W) equals the bipartite homomorphism density t_bip(H,W). The two integrals of Definition 15 have the same integrand: the vertices of the two parts of B range over the same two variables as the parts of H, and the edges of B are exactly the directed pairs across the parts. In the mission the statement is the equality of tIn and tInBip on the orientation, and its proof is a change of variables between the two exponentials - the sum type against the product of the two parts - carried by the transport and Fubini axioms of the directed graphon interface.
--
--   **Formalization Note** The equality is the bridge that makes the two Sidorenko properties comparable; no finiteness or measurability hypotheses appear beyond the graphon interface.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 2.2 (Observation 16, page 7).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 1 (Observation 16): directed and bipartite densities agree
on the orientation. Let H be a bipartite graph and let orientOf H be the
oriented graph obtained by directing every edge from the first part to
the second. For every directed graphon, the homomorphism density of
orientOf H equals the bipartite homomorphism density of H. The two
integrals of Definition 15 of the paper have the same integrand, the
first parts of the two vertex tuples ranging over the same sum type. -/
theorem bip_dir_density (dg : DirGraphon) (m n : ℕ) (H : BipGraph m n) :
    dg.tIn (orientOf H) = dg.tInBip H := by sorry

end DirS
