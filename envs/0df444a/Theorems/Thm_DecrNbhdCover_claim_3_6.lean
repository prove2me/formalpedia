-- Prove2me | Theorems.Thm_DecrNbhdCover_claim_3_6
-- name    : DecrNbhdCover.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:19.722368+00:00
-- url     : https://prove2.me/theorems/1161d394-4e07-4c9e-b1b6-a38dfb13a6f3
-- title:
--   Claim 3.6 — Property Q1 implies Property P3
-- statement:
--   Let $G$ and $H$ be static graphs, with $H=(V,U,E(H),\ell_H)$ well-structured and $V=V(G)$. If Property Q1 holds for $G$ and $H$ with respect to parameters $\epsilon,d,D$, then Property P3 holds for them with the same parameters: for all $u,v\in V(G)$,
--   $$\mathrm{dist}_H(u,v)\le(1+\epsilon)\mathrm{dist}_G(u,v)+\epsilon D.$$
--
--   So the local property gives the global distance bound.
--
--   Differences from the source:
--   - reading: "every path $P$" in Property Q1 → every simple path; reason: $P[v,a]$ and "$a\in V(P)\setminus\{v\}$" are used for simple paths: the proof in C.2 takes "the vertex that lies furthest from $v$ on $P$", and on a walk returning to $v$ its choice of $a$ can equal $v$
--   - encoding: "some parameters" → $0<\epsilon<1$ and $0<d\le D$, with $d$ a natural number; reason: this is the standing choice on p.18 ("Consider parameters $0<\epsilon<1$ and $0<d\le D$"), and $d$ is an integer in Definition 3.2
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Claim 3.6, p.19 (PDF 23)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-- **Claim 3.6.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.19 (PDF 23).

"Let G and H be a pair of static graphs, and assume that H = (V, U, E(H), ℓH(·)) is a well-structured graph with V = V(G). Assume further that Property Q1 holds for G and H with respect to some parameters ϵ, d and D. Then Property P3 holds for G and H with respect to ϵ, d and D as well."

**Formalization Note.** The parameters are those fixed just before Q1 on p.18: "Consider parameters 0 < ϵ < 1 and 0 < d ≤ D". Here `d` is a natural number, as in Definition 3.2. -/
theorem claim_3_6 {α β ε η : Type} (G : Graph α ε) (H : WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ)
    (hG : G.WF) (hH : H.WF) (hV : H.V = G.V) (heps : 0 < eps) (heps1 : eps < 1) (hd : 0 < d)
    (hdD : (d : ℝ) ≤ D) (hQ : Q1 G H eps d D) : P3 G H eps D := by sorry

end DecrNbhdCover
