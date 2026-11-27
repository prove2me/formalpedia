-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_Supplement_theorem_2
-- name    : AtomicDynRouting.ResidenceTime.Supplement.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:33:00.713147+00:00
-- url     : https://prove2.me/theorems/94d9b336-a353-4dbc-b29d-446a15341a2f
-- title:
--   Theorem 2, p. 11 — with uniform capacity c and simultaneous entry, ζ's residence time is at most Loζdζ + ⌊(|Δ| − 1)/c⌋
-- statement:
--   Let $G=(V,E)$ be a finite acyclic network, $c\ge1$ an integer, and consider an atomic dynamic routing on $G_c$ (every edge of unit length and capacity $c$; at each integer time exactly $\min\{c,n\}$ of the $n$ agents in a buffer leave it) with a finite set $\Delta$ of agents, possibly with different OD pairs, all of whom enter the network at the same time. Then every agent $\zeta$, with origin $o_\zeta$ and destination $d_\zeta$, exits, and his residence time satisfies
--   $$\text{residence time of }\zeta\ \le\ L_{o_\zeta d_\zeta}+\left\lfloor\frac{|\Delta|-1}{c}\right\rfloor,$$
--   where $L_{o_\zeta d_\zeta}$ is the length of a longest $o_\zeta$-$d_\zeta$ path in $G$.
--
--   For $c=1$ the bound is $L_{o_\zeta d_\zeta}+|\Delta|-1$; the result generalizes the bound of Mansour and Patt-Shamir for shortest-path routing to arbitrary routes in acyclic networks.
--
--   **Formalization Note** The residence time is the base model's `residenceTime` in $\mathbb N\cup\{\infty\}$ ($\infty$ if $\zeta$ never exits), so the inequality also asserts that $\zeta$ exits. The floor is natural-number division.
--
--   Differences from the source:
--
--   - encoding: all |Δ| agents enter G_c at the same time (§4 text: at the very beginning) → Fintype ι and a common entry time R.entry i = R.entry j for all i, j; reason: the theorem says 'at the same time'; shifting the common time changes no residence time, and time 0 is the case R.entry = 0
--   - encoding: residence time of ζ → base residenceTime in ℕ∞ (⊤ if ζ never exits); reason: the finite bound forces ζ to exit, as the source asserts
--   - encoding: the number n of agents in a buffer → the number of (agent, route position) pairs at that edge; reason: routes are paths of an acyclic network, so each agent occupies a given buffer at most once
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 11 (PDF 12), Theorem 2 (model: p. 10, PDF 11, §4)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_CapacityRun

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem theorem_2 {ι V E : Type} [Fintype ι] [Fintype V] [Fintype E] (N : Network V E) (hN : N.Acyclic) (c : ℕ) (hc : 0 < c) (R : RunData ι E V) (hR : IsADRc N c R) (hsame : ∀ i j, R.entry i = R.entry j) (ζ : ι) : R.residenceTime ζ ≤ ((N.longest (R.orig ζ) (R.dest ζ) + (Fintype.card ι - 1) / c : ℕ) : ℕ∞) := by sorry

end AtomicDynRouting.ResidenceTime.Supplement
