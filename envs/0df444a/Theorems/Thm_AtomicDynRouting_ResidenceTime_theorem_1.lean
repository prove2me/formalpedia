-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_theorem_1
-- name    : AtomicDynRouting.ResidenceTime.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:15.434661+00:00
-- url     : https://prove2.me/theorems/888a9a5e-7721-4615-9e6e-238e2c240320
-- title:
--   Theorem 1, p. 7 — if no later entrant exits Gζ before ζ, then ζ exits by r0 + Loζdζ + |Bζ,p(r0)|
-- statement:
--   Let $G=(V,E)$ be a finite acyclic directed multigraph in which every edge has unit length and unit capacity, and take an atomic dynamic routing on $G$ obeying the buffer regulations (A1)–(A2), with any choice of the agent leaving each buffer. Fix an agent $\zeta$ with entry time $r$, origin $o_\zeta$ and destination $d_\zeta$, and let $G_\zeta$, $A_{\zeta,p}$, $B_{\zeta,p}(r_0)$ and $L_{o_\zeta d_\zeta}$ be as in §3.1.
--
--   For any integer time $r_0\ge r$: if no agent in $A_{\zeta,p}$ exits $G_\zeta$ before agent $\zeta$ exits $G$, then $\zeta$ exits $G$ no later than
--   $$r_0+L_{o_\zeta d_\zeta}+\bigl|B_{\zeta,p}(r_0)\bigr|.$$
--
--   The bound holds whatever rule selects the leaving agent of a buffer. Taking $r_0=r$ when no agent enters after $\zeta$ on $G_\zeta$ gives Corollary 1: the residence time of $\zeta$ is at most $L_{o_\zeta d_\zeta}+|B_{\zeta,p}(r)|$. The paper uses the family of bounds parameterised by $r_0$ to settle the queue-length question for equilibria on series-parallel networks (§6).
--
--   **Formalization Note.** Exit times live in $\mathbb N\cup\{\infty\}$ (`ℕ∞`); the conclusion forces $\zeta$'s exit time to be finite. The hypothesis is strict: for each $i\in A_{\zeta,p}$ it is excluded that the time $i$ reaches the sink of his route $\cap\,G_\zeta$ is earlier than $\zeta$'s exit time. $|B_{\zeta,p}(r_0)|$ is `Set.ncard`; the set is finite because its agents entered by time $r$, finitely many per time. The theorem assumes only $r_0\ge r$, as printed; if $\zeta$ has already exited by $r_0$, the bound holds trivially.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 7 (PDF 8), Theorem 1

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Model

namespace AtomicDynRouting.ResidenceTime

/-- Theorem 1 (Cao–Chen–Chen–Wang, p. 7). Given an ADR profile on a unit-capacity acyclic network,
for any integer time `r0 ≥ r` (`r` the entry time of `ζ`), if no agent in `A_{ζ,p}` exits `Gζ`
before `ζ` exits `G`, then `ζ` exits `G` no later than `r0 + L_{oζdζ} + |B_{ζ,p}(r0)|`. -/
theorem theorem_1 {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hA : ∀ i ∈ Aset N R ζ, ¬ (exitGz N R ζ i < R.exitTime ζ)) : R.exitTime ζ ≤ ((r0 + N.longest (R.orig ζ) (R.dest ζ) + (Bset N R ζ r0).ncard : ℕ) : ℕ∞) := by sorry

end AtomicDynRouting.ResidenceTime
