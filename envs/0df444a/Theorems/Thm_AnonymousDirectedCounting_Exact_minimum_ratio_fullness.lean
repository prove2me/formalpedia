-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_minimum_ratio_fullness
-- name    : AnonymousDirectedCounting.Exact.minimum_ratio_fullness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:40.92865+00:00
-- url     : https://prove2.me/theorems/a0408855-5410-406e-ac72-267e70e16c5a
-- title:
--   Lemma 3 — minimum ratio forces fullness
-- statement:
--   Assume a candidate passes Steps 1–4 on the round-$t$ vista of an agent, with anchor $h$, and let $1\le r\le h$. Let $\alpha=\min_{v\in\mathcal L_r}a(v)/b(v)$, let $\mathcal D$ be the nodes attaining it, and let $\mathcal Q$ be their parents. If
--   $$
--   \bigcup_{u\in\mathcal Q}A(u)=\bigcup_{v\in\mathcal D}A(v),
--   $$
--   then $\mathcal L_r$ is full and every node of it has ratio $\alpha$. This is where the candidate flow equations and strong connectivity combine.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - generalization: the credit lemmas stated for the core test (final level m at round 2m − 1), and said on printed p. 19 to apply unchanged to the sharp test → any final level k, any round t and any candidate m passing Steps 1–4; reason: the proofs read only Steps 1–4; k = m, t = 2m − 1 is the source's core case and k = m − 1, t = 2m − 2 its sharp case
--   - encoding: candidate anonymities b(v) defined on the visible nodes up to the anchor → a total family b : (r : ℕ) → History r → ℚ constrained only on visible nodes at levels at most h; reason: values elsewhere are unconstrained and never read, and the checks determine the visible values uniquely
--   - encoding: α = min_{v∈L_r} ρ(v) → a variable α with IsLeast of the image of L_r under the ratio; reason: L_r is nonempty for r at most h, so such an α exists and is the minimum
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 3, printed p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 3, printed p. 8 (PDF p. 10), under the standing assumption of printed p. 7: the candidate
passes Steps 1-4, `r = i + 1` ranges over `1, ..., h`, `α` is the minimum ratio on `L_r`, `D` the
nodes attaining it and `Q` their parents. -/
theorem minimum_ratio_fullness {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (k m t : ℕ) (x : Fin n) (h : ℕ) (b : (r : ℕ) → History r → ℚ)
    (hpass : PassesStepsOneToFour G.leaders.card k m (history G t x) h b)
    (i : ℕ) (hi : i + 1 ≤ h) (α : ℚ)
    (hα : IsLeast (ratio G b (i + 1) '' (agentLevel G t x (i + 1) : Set (History (i + 1)))) α)
    (hunion : unionFibers G i (parentsOf (minRatioNodes G t x b (i + 1) α)) =
      unionFibers G (i + 1) (minRatioNodes G t x b (i + 1) α)) :
    IsFull G t x (i + 1) ∧ ∀ v ∈ agentLevel G t x (i + 1), ratio G b (i + 1) v = α := by sorry

end AnonymousDirectedCounting.Exact
