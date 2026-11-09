-- Prove2me | Theorems.Thm_AnonymousDirectedCounting_Exact_credit_conservation
-- name    : AnonymousDirectedCounting.Exact.credit_conservation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:27.166791+00:00
-- url     : https://prove2.me/theorems/7e9c59a0-c1d1-4683-94d0-b8d675dc8088
-- title:
--   Lemma 4 — credit conservation detects the true size
-- statement:
--   Assume a candidate $m$ passes Steps 1–4 on the round-$t$ vista of an agent, with anchor $h$. For every $1\le r\le h$,
--   $$
--   \Phi_r\le\Phi_{r-1},
--   $$
--   and if equality holds for any such $r$, then $m=n$. Together with the suffix check, this rules out every premature candidate in the proof of Theorem 1. The lemma does not assume $m<n$.
--
--   Differences from the source:
--   - encoding: anonymous agents and abstract history-tree nodes with fibers → external Fin n indexing, and nodes as values of History r with fibers computed from the network; reason: the index is absent from protocol inputs; two agents have equal History r exactly when they lie in one class of P_r, so nodes and vistas up to isomorphism are the same data
--   - generalization: the credit lemmas stated for the core test (final level m at round 2m − 1), and said on printed p. 19 to apply unchanged to the sharp test → any final level k, any round t and any candidate m passing Steps 1–4; reason: the proofs read only Steps 1–4; k = m, t = 2m − 1 is the source's core case and k = m − 1, t = 2m − 2 its sharp case
--   - encoding: candidate anonymities b(v) defined on the visible nodes up to the anchor → a total family b : (r : ℕ) → History r → ℚ constrained only on visible nodes at levels at most h; reason: values elsewhere are unconstrained and never read, and the checks determine the visible values uniquely
-- source:
--   Giuseppe A. Di Luna, Giovanni Viglietta, STOC 2027 submission #455 (October 2026), Lemma 4, printed p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_AnonymousDirectedCounting_Exact_CandidateTest

set_option autoImplicit false

namespace AnonymousDirectedCounting.Exact

/-- Lemma 4, printed p. 8 (PDF p. 10), under the standing assumption of printed p. 7: the candidate
passes Steps 1-4 and `r = i + 1` ranges over `1, ..., h`. -/
theorem credit_conservation {n : ℕ} (G : NetworkModel n) (hG : Admissible G)
    (k m t : ℕ) (x : Fin n) (h : ℕ) (b : (r : ℕ) → History r → ℚ)
    (hpass : PassesStepsOneToFour G.leaders.card k m (history G t x) h b) :
    (∀ i : ℕ, i + 1 ≤ h → totalCredit G t x b (i + 1) ≤ totalCredit G t x b i) ∧
      (∀ i : ℕ, i + 1 ≤ h → totalCredit G t x b (i + 1) = totalCredit G t x b i → m = n) := by sorry

end AnonymousDirectedCounting.Exact
