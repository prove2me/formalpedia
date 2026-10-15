-- Prove2me | Theorems.Thm_FairGuarantees_DivideChoose_invariant
-- name    : FairGuarantees.DivideChoose.invariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:36.518159+00:00
-- url     : https://prove2.me/theorems/6fa72dcd-c9c7-484d-b1e3-d2b84c0a2e23
-- title:
--   Proof of Theorem 1 i), p. 15 — shares already assigned are worth less than minMax(u; n) to an unserved strategic agent
-- statement:
--   Consider a play of the D&C$_n$ rule ($n\ge1$) in which agent $i$ with utility $u$ follows the minMax strategy of Theorem 1 i), and suppose $i$ is still unserved after the steps played so far. Then every share $T$ assigned at those steps satisfies
--   $$u(T)<\mathrm{minMax}(u;n).$$
--
--   The reason is properness of the matching: $i$ was not served, so $i$ liked none of the assigned shares, and $i$ likes every share worth at least $\mathrm{minMax}(u;n)$. The invariant feeds both the chooser and the Divider steps of the proof.
--
--   **Formalization Note** The play is any valid (possibly incomplete) prefix `run`; "unserved" is `i ∈ nextAgents run`. The statement does not need $u\in\mathcal D(\Omega)$ or properties of $\Omega$, so they are not assumed.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 15, §4, proof of Theorem 1, Statement i), first paragraph

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_DivideChoose_DCRule

namespace FairGuarantees.DivideChoose

/-- Proof of Theorem 1 i), p. 15, first paragraph: in a valid play of D&C_n in which agent `i`
follows the minMax strategy and is still unserved, every share assigned so far (to other
agents) is worth to `i` strictly less than `minMax(u; n)`. -/
theorem invariant {d n : ℕ} (hn : 0 < n) {Ω : Set (E d)} {u : Set (E d) → ℝ} (i : Fin n)
    (run : List (DCStep d n)) (hrun : IsValidPrefix Ω run)
    (hstrat : FollowsMinMaxStrategy Ω u i run) (hi : i ∈ nextAgents run) :
    ∀ s ∈ run, ∀ a ∈ Matched s, u (assignedPart s a) < minMax Ω u n := by sorry

end FairGuarantees.DivideChoose
