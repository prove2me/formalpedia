-- Prove2me | Theorems.Thm_DynOracleConn_epoch_answer
-- name    : DynOracleConn.epoch_answer
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:54:43.479508+00:00
-- url     : https://prove2.me/theorems/28e27a37-4d14-4e9b-901f-21af9ef5131a
-- title:
--   §3.1.2, p.21 — during an epoch, $s,t$ are connected iff $y_{I_i}=0$
-- statement:
--   Let $i$ be the item queried in an epoch. After the insertion of $\{t,v^0_i\}$ into $\mathcal G_n(\pi,z)$, the vertices $s$ and $t$ are connected if and only if $y_i=0$. In $\mathcal G_n(\pi,z)$ itself, which is the graph after the deletion, they are not connected.
--
--   Hence every correct connectivity answer during the stream either answers a PPHP query or is the constant answer "not connected".
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: d = ⌊(n−2)/8⌋ and one vertex layout → any injection e of the named vertices into Fin n; reason: the paper's layout is one such injection
--   - generalization: the paragraph describes the current graph during the query → an added clause: s and t are not connected in the graph after the deletion; reason: it contains the printed statement; t is isolated there (p.20)
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1.2, p.21

import Mathlib
import Definitions.Def_DynOracleConn_Gadget

namespace DynOracleConn

/-- **§3.1.2, p.21 — the answer of an epoch.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1.2, p.21: "the query asked at epoch i
is equivalent to asking which path v⁰_{Iᵢ} is on, since s and t are connected if and only if s and
v⁰_{Iᵢ} are on the same path … Claim 3.1 shows that y_{Iᵢ} is 1 if and only if s and t are not
connected in the current graph."

After the insertion of `{t, v⁰ᵢ}`, `s` and `t` are connected iff `y_i = false`; after its
deletion (and during the insertion phase's end state 𝒢ₙ(π, z)), they are not connected. -/
theorem epoch_answer {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) (i : Fin d) :
    ((withT e X i).Reachable (e GV.s) (e GV.t) ↔ yval X i = false) ∧
    ¬ (gadget e X).Reachable (e GV.s) (e GV.t) := by sorry

end DynOracleConn
