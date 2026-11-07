-- Prove2me | Theorems.Thm_DynOracleConn_claim_3_1
-- name    : DynOracleConn.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:50.162587+00:00
-- url     : https://prove2.me/theorems/2b472db5-df47-4309-9d25-9633acd9a521
-- title:
--   Claim 3.1, p.21 — $v^0_i$ lies on path 0 iff $y_i=0$
-- statement:
--   Let $\mathcal G_n(\pi,z)$ be the graph of §3.1, let $i$ be an item, and let $y_i=\bigoplus_{k\in[\pi(i)]}z_k$. Then
--
--   $$v^0_i\text{ is connected to }s\text{ in }\mathcal G_n(\pi,z)\iff y_i=0.$$
--
--   Path $0$ is the component of $s$. The claim identifies a connectivity query in the graph with a prefix parity of the switch bits, which is what the reduction from PPHP rests on.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: d = ⌊(n−2)/8⌋ and one vertex layout → any injection e of the named vertices into Fin n; reason: the paper's layout is one such injection
--   - encoding: lies on path 0 → is reachable from s; reason: path 0 is defined as the path containing s; same statement
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Claim 3.1, p.21

import Mathlib
import Definitions.Def_DynOracleConn_Gadget

namespace DynOracleConn

/-- **Claim 3.1, p.21.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Claim 3.1, p.21: "For every item i, the vertex v⁰ᵢ lies on path 0
if and only if yᵢ = ⊕_{k∈[π(i)]} z_k = 0."

Path 0 is the component of `s`; so the claim reads: `v⁰ᵢ` is connected to `s` in 𝒢ₙ(π, z) exactly
when `y_i = false`.

**Formalization Note.** 0-based: `y_i = ⊕_{k ≤ π i} z_k` (`yval`). -/
theorem claim_3_1 {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    (gadget e X).Reachable (e GV.s) (e (GV.v false i)) ↔ yval X i = false := by sorry

end DynOracleConn
