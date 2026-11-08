-- Prove2me | Theorems.Thm_DecrNbhdCover_claim_3_11
-- name    : DecrNbhdCover.claim_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:07.936877+00:00
-- url     : https://prove2.me/theorems/db69c844-d972-43ff-a70f-fd35ff349eca
-- title:
--   Claim 3.11 — $H_C$ is a partial $(\epsilon,d,D)$-emulator for $G[C]$
-- statement:
--   Let $G$ be a decremental graph, $H=(V,U,E(H),\ell_H)$ a partial $(\epsilon,d,D)$-emulator for $G$, and $C\subseteq V(G)$ a **decremental** cluster of $G$. Then the subgraph $H_C\subseteq H$ associated with $C$ is a partial $(\epsilon,d,D)$-emulator for $G[C]$.
--
--   This is what lets subroutines run inside a cluster.
--
--   Differences from the source:
--   - reading: "every path $P$" in Property Q1 → every simple path; reason: $P[v,a]$ and "$a\in V(P)\setminus\{v\}$" are used for simple paths: the proof in C.2 takes "the vertex that lies furthest from $v$ on $P$", and on a walk returning to $v$ its choice of $a$ can equal $v$
--   - encoding: "some parameters" → $0<\epsilon<1$ and $0<d\le D$, with $d$ a natural number; reason: this is the standing choice on p.18 ("Consider parameters $0<\epsilon<1$ and $0<d\le D$"), and $d$ is an integer in Definition 3.2
--   - encoding: a cluster that exists "from the time it is created" → a creation time $\tau_0$; both sides of the conclusion are indexed from $\tau_0$; reason: time before the cluster exists is irrelevant
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Claim 3.11, p.20 (PDF 24); Definition 3.10, p.20 (PDF 24)

import Mathlib
import Definitions.Def_DecrNbhdCover_Emulator

set_option autoImplicit false

namespace DecrNbhdCover

open scoped ENNReal

/-- **Claim 3.11.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.20 (PDF 24).

"Let G be a decremental graph and let H = (V, U, E(H), ℓH(·)) be a partial (ϵ, d, D)-emulator for G. Let C ⊆ V(G) be a decremental cluster of G. Then the subgraph H_C ⊆ H associated with C is a partial (ϵ, d, D)-emulator for G[C]."

**Formalization Note.** The cluster is created at time `τ₀`: `C t` is the cluster `t` steps later, and it stays inside `V(G)`. Time in the conclusion starts at `τ₀`. -/
theorem claim_3_11 {α β ε η : Type} (G : ℕ → Graph α ε) (H : ℕ → WSGraph α β η) (eps : ℝ) (d : ℕ) (D : ℝ)
    (heps : 0 < eps) (heps1 : eps < 1) (hd : 0 < d) (hdD : (d : ℝ) ≤ D)
    (hG : ∀ τ, (G τ).WF) (hH : IsPartialDyn G H eps d D)
    (τ₀ : ℕ) (Cl : ℕ → Set α) (hC : ∀ t, Cl (t + 1) ⊆ Cl t) (hCG : ∀ t, Cl t ⊆ (G (τ₀ + t)).V) :
    IsPartialDyn (fun t => (G (τ₀ + t)).induced (Cl t)) (fun t => (H (τ₀ + t)).assocSub (Cl t)) eps d D := by sorry

end DecrNbhdCover
