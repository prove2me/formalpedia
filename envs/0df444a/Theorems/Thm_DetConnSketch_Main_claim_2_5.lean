-- Prove2me | Theorems.Thm_DetConnSketch_Main_claim_2_5
-- name    : DetConnSketch.Main.claim_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:23.385975+00:00
-- url     : https://prove2.me/theorems/8e2d5058-17b7-45ed-8643-dff4d4ea7b11
-- title:
--   Claim 2.5 — a connectivity protocol on $n+1$ vertices solves connected components on $n$ vertices with the same message
-- statement:
--   Let $(\mathrm{msg}, \mathrm{dec})$ be a deterministic one-way connectivity protocol on $n+1$ labeled vertices with $m$-bit messages. Then there is a deterministic one-way connected-components protocol on $n$ vertices with $m$-bit messages whose message for $G_A$ is exactly
--   $$\mathrm{msg}(G_A^\star),$$
--   where $G_A^\star$ adds a new vertex $\star$ joined to every vertex of $G_A$; Bob decodes the components of $G_A - G_B$ from it and $G_B$.
--
--   With Claim 2.2 and Theorem 8.1 this gives the lower clause of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: the protocol 'also solves' the connected-components problem on n vertices → ∃ Q : CompProtocol (Fin n) m with Q.msg G = P.msg (apexGraph G) for every G; reason: 'using the exact same message' (p. 1); Bob's decoder is existential
--   - encoding: n + 1 vertices, new vertex ⋆ → Fin (n + 1) with ⋆ = Fin.last n and the old vertices Fin.castSucc; reason: a fixed labelling of the n + 1 vertices
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 15 (PDF 19), Claim 2.5

import Mathlib
import Definitions.Def_DetConnSketch_Main_Protocol
import Definitions.Def_DetConnSketch_Main_ApexGraph

namespace DetConnSketch.Main

/-- Claim 2.5: a deterministic one-way connectivity protocol `P` on `n + 1` vertices also solves
the connected-components problem on `n` vertices with the exact same message: Alice sends
`P.msg` of her graph with a new vertex `⋆` joined to every vertex, and some decoder for Bob
outputs the connected components of `GA − GB`. -/
theorem claim_2_5 (n m : ℕ) (P : ConnProtocol (Fin (n + 1)) m) :
    ∃ Q : CompProtocol (Fin n) m, ∀ G : SimpleGraph (Fin n), Q.msg G = P.msg (apexGraph G) := by sorry

end DetConnSketch.Main
