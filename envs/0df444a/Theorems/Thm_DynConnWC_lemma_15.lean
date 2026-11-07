-- Prove2me | Theorems.Thm_DynConnWC_lemma_15
-- name    : DynConnWC.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:24.160163+00:00
-- url     : https://prove2.me/theorems/d1f1a5d0-9484-4869-b1d1-c12f3db61d2a
-- title:
--   Lemma 15 — $\Pr[\text{not }E_2]\le3T_0L(J+1)2^{J-w}$
-- statement:
--   For a fixed valid update sequence with at most $T_0$ updates, let $E_2$ be the event that, for every update, level $i$, lower tree searched by `UpdateWeights`$_i$ and threshold $j\in\{0,\dots,J\}$, the fingerprint test of $C_i$ at $j$ passes only if the selected cut edges are the decoded edge alone. Then
--   $$\Pr[\text{not }E_2]\le3T_0L(J+1)2^{J-w}.$$
--   This bounds the errors of the verification at all levels, so returned pairs are graph edges with high probability.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
--   - generalization: $T_0=\lceil n^d\rceil$ → any $T_0$ at least the number of updates; reason: the bound and its proof use only that $T_0$ bounds the updates; $T_0=\lceil n^d\rceil$ is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 15, p.19 (PDF 20)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Lemma 15 (Soundness at the levels).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.19 (PDF 20).
"Let E2 be the event that, for every weight-update search, the fingerprint test is sound at every
sampling threshold. … Then Pr[not E2] ≤ 3T0L(J + 1)2^{J−w}."

**Formalization Note.** The sequence is fixed in advance, valid, with at most `T0` updates; `S` is any
setup meeting the standing assumptions, in any search mode. -/
theorem lemma_15 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ) (T0 : ℕ)
    (hT0 : σ.length ≤ T0) :
    probR S {R | ¬ E2 S R σ} ≤
      3 * (T0 : ℝ) * Lpar n * (Jbits n + 1) * (2 : ℝ) ^ ((Jbits n : ℤ) - S.w) := by sorry

end DynConnWC
