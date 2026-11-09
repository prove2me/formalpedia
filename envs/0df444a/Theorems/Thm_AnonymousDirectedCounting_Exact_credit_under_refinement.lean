-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_credit_under_refinement
-- name    : AnonymousDirectedCounting.Exact.credit_under_refinement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:32.157075+00:00
-- url     : https://prove2.me/theorems/cea14050-6a71-4f77-95a2-e4ae3008f90e
-- title:
--   Lemma 2 — credit under refinement
-- statement:
--   Assume a candidate $m$ passes Steps 1–4 on the round-$t$ vista of an agent, with anchor $h$ and candidate anonymities $b$, and let $1\le r\le h$. Let $u\in\mathcal L_{r-1}$ with children $v_1,\dots,v_k$ in $\mathcal L_r$. Then
--   $$
--   \sum_{i=1}^k c(v_i)\le c(u).
--   $$
--   If equality holds and $a(v_j)\le b(v_j)$ for some child, then $u$ has exactly one child $v_1$, with $A(v_1)=A(u)$ and $b(v_1)=b(u)$. This compares a node's credit with that of its children, using disjoint refinement and backward propagation.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - generalization: the credit lemmas stated for the core test (final level m at round 2m − 1), and said on printed p. 19 to apply unchanged to the sharp test → any final level k, any round t and any candidate m passing Steps 1–4; reason: the proofs read only Steps 1–4; k = m, t = 2m − 1 is the source's core case and k = m − 1, t = 2m − 2 its sharp case
--   - encoding: candidate anonymities b(v) defined on the visible nodes up to the anchor → a total family b : (r : ℕ) → History r → ℚ constrained only on visible nodes at levels at most h; reason: values elsewhere are unconstrained and never read, and the checks determine the visible values uniquely
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 2, printed p. 7 (PDF p. 9)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 2, printed p. 7 (PDF p. 9), under the standing assumption of that page: the candidate
passes Steps 1-4, and `r = i + 1` ranges over `1, ..., h`. -/
theorem credit_under_refinement {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (k m t : ℕ) (x : Fin n) (h : ℕ) (b : (r : ℕ) → History r → ℚ)
    (hpass : PassesStepsOneToFour G.leaders.card k m (history G t x) h b)
    (i : ℕ) (hi : i + 1 ≤ h) (u : History i) (hu : u ∈ agentLevel G t x i) :
    ∑ v ∈ childrenIn (history G t x) i u, credit G b (i + 1) v ≤ credit G b i u ∧
      (∑ v ∈ childrenIn (history G t x) i u, credit G b (i + 1) v = credit G b i u →
        (∃ v ∈ childrenIn (history G t x) i u, (anonymity G (i + 1) v : ℚ) ≤ b (i + 1) v) →
          ∃ v₁, childrenIn (history G t x) i u = {v₁} ∧
            fiberOf G (i + 1) v₁ = fiberOf G i u ∧ b (i + 1) v₁ = b i u) := by sorry

end AnonymousDirectedCounting.Exact
