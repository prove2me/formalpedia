-- Prove2me | Theorems.Thm_ErasureQTanner_ramanujan_complexes
-- name    : ErasureQTanner.ramanujan_complexes
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:50.042491+00:00
-- url     : https://prove2.me/theorems/5d8511ee-11af-4d01-bf8c-b6872d8c7198
-- title:
--   §4, p.7 — Ramanujan square complexes of arbitrarily large degree
-- statement:
--   For arbitrarily large $\Delta$ and for every $m$, there is a group $G$ with $|G|\ge m$ and symmetric generating sets $A,B$ of size $\Delta$ such that $\mathrm{Cay}(A,G)$ and $\mathrm{Cay}(G,B)$ are non-bipartite Ramanujan graphs. This is the expander input the paper assumes when it says the square complex should be chosen with good expansion.
--
--   Differences from the source:
--   - reading: a choice of $G,A,B$ with Ramanujan Cayley graphs → for arbitrarily large $\Delta$ and every size $m$, a non-bipartite complex with $|G|\ge m$; reason: the paper needs a sequence of complexes at a large fixed degree (p.4, p.26) and gives no citation; non-bipartite is the setting of [LZ23]; Lubotzky–Phillips–Sarnak supply it
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §4, p.7

import Mathlib
import Definitions.Def_ErasureQTanner_LRData

set_option autoImplicit false

namespace ErasureQTanner

/-- **Ramanujan square complexes** (§4, p.7, unnumbered). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.7: "we chose the group `G` and the generating sets `A` and
`B` so that associated Cayley graphs `Cay(A, G)` and `Cay(G, B)` are Ramanujan graphs"; the length `∆` "can be arbitrarily large".

**Formalization Note.** The paper gives no citation for existence; the standard source is Lubotzky–Phillips–Sarnak. For
arbitrarily large `Δ` and every size `m` there is a complex with `|G| ≥ m`, non-bipartite Ramanujan on both sides. -/
theorem ramanujan_complexes : ∀ Δ₀ : ℕ, ∃ Δ : ℕ, Δ₀ ≤ Δ ∧ ∀ m : ℕ, ∃ Γ : LRData Δ,
    m ≤ Fintype.card Γ.G ∧ Γ.IsRamanujan := by sorry

end ErasureQTanner
