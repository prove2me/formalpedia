-- Prove2me | Theorems.Thm_DetDLP_w3_m5_lookup_subdivision
-- name    : DetDLP.w3_m5_lookup_subdivision
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T21:20:14.356902+00:00
-- url     : https://prove2.me/theorems/28894c09-e441-4227-b454-e121bc3bffca
-- title:
--   Stage II: M5 equality subdivision gives the terminal lookup specification
-- statement:
--   A loopless wire graph has exactly $4m$ designated lookup vertices, each of degree $k$. Orient their incident wires outwards and suppose all nonlookup degrees are at most $D$, with $2\le D$ and doubled edge count at most $S$. M5 subdivision produces a bipartite graph satisfying the complete lookup separator specification. Its terminal vertices are exactly the equality vertices on the $4mk$ distinct outgoing address wires, each with one lookup neighbor and one core neighbor.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_TerminalBTN
import Definitions.Def_DetDLP_W4_M5Subdivision
set_option autoImplicit false
open DetDLP DetDLP.w4_M5Network

theorem DetDLP.w3_m5_lookup_subdivision (G : WireGraph) (L : Finset (Fin G.nV)) (m k S D : ℕ)
    (hcount : L.card = 4*m) (hlook : ∀ v ∈ L, G.deg v = k)
    (horient : ∀ e, (G.endpoints e).2 ∉ L)
    (hedge : 2*G.nE ≤ S) (hcore : ∀ v ∉ L, G.deg v ≤ D) (hD : 2 ≤ D) :
    ∃ s : LookupSeparatorSpec G.subdivision m k S D,
      s.lookupVerts = L.image G.oldVertex ∧ s.termSubdivVerts =
        (Finset.univ.filter fun e : Fin G.nE => (G.endpoints e).1 ∈ L).image G.equalityVertex := by sorry
