-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_flat_level_recovery
-- name    : AnonymousDirectedCounting.Exact.flat_level_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:23.519312+00:00
-- url     : https://prove2.me/theorems/6845e2be-0486-4ad7-aa41-311398211e3e
-- title:
--   Lemma 1 — unique recovery at a full flat level
-- statement:
--   Let $G$ be an admissible network, let $x$ be an agent, let $t$ be a round and let $r\ge1$. Assume level $\mathcal L_r$ of the round-$t$ vista of $x$ is full and flat. The anonymities satisfy the flow equations on $\mathcal L_r$ with the leader equation $\sum_{v\text{ leader}}b(v)=\ell$, and every real solution agrees with them:
--   $$
--   b(v)=a(v)\qquad(v\in\mathcal L_r).
--   $$
--   Existence and uniqueness are conclusions. This is the algebraic step that lets the true candidate pass the test once fullness is known by other means.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - generalization: the flow equations together with ℓ uniquely determine the anonymities → the anonymities solve the system, and every real solution equals them on the level; reason: Appendix A proves the real form; it specializes to the rational uniqueness used in Step 3
--   - encoding: one unknown for each node of the level → a total function on History r with equality required only on the level; reason: values off the level occur in no equation
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 1, printed p. 6 (PDF p. 8); Appendix A, printed pp. 17–18 (PDF pp. 19–20)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_HistoryTree

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 1, printed p. 6 (PDF p. 8), proof in Appendix A, printed pp. 17-18 (PDF pp. 19-20). On a
full flat level `L_r`, `r ≥ 1`, the anonymities solve the flow equations with the leader equation,
and every real solution equals them on `L_r`. -/
theorem flat_level_recovery {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (t : ℕ) (x : Fin n) (r : ℕ) (hr : 1 ≤ r)
    (hfull : IsFull G t x r) (hflat : IsFlatLevel (history G t x) r) :
    FlowSystem ℝ G.leaders.card (history G t x) r (fun v => (anonymity G r v : ℝ)) ∧
      ∀ b : History r → ℝ, FlowSystem ℝ G.leaders.card (history G t x) r b →
        ∀ v ∈ agentLevel G t x r, b v = (anonymity G r v : ℝ) := by sorry

end AnonymousDirectedCounting.Exact
