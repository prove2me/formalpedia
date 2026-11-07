-- Prove2me | Theorems.Thm_DynConnWC_lemma_21
-- name    : DynConnWC.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:39:26.933879+00:00
-- url     : https://prove2.me/theorems/d086dd19-a011-461a-8bbe-d8da32dbd7dd
-- title:
--   Lemma 21 — $\Pr[\text{not }E_3]\le T_02^h(7/8)^r$, $\Pr[\text{not }E_4]\le T_02^hr(J+1)2^{J-w}$
-- statement:
--   For a fixed valid update sequence with at most $T_0$ updates, let $E_3$ be the event that for every update $t$ and every cut in $K_t$ some final instance has a threshold selecting exactly one edge of the cut, and $E_4$ the event that the fingerprint test is sound for every update, cut in $K_t$, final instance and threshold. Then
--   $$\Pr[\text{not }E_3]\le T_02^h(7/8)^r,\qquad\Pr[\text{not }E_4]\le T_02^hr(J+1)2^{J-w}.$$
--   This is what keeps the final repair searches correct over the whole sequence, even though the searched trees depend on earlier answers.
--
--   Differences from the source:
--   - generalization: the data structure of §3 with the Euler-tour search of Appendix B.2 → any function of the two forests and two vertices meeting Lemma 7's specification, and any search mode; reason: the analysis uses only the specification and determinism; B.2's search with the plain mode is one instance
--   - generalization: $T_0=\lceil n^d\rceil$ → any $T_0$ at least the number of updates; reason: the bound and its proof use only that $T_0$ bounds the updates; $T_0=\lceil n^d\rceil$ is one instance
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Lemma 21, p.22 (PDF 23)

import Mathlib
import Definitions.Def_DynConnWC_Events

set_option autoImplicit false

namespace DynConnWC

/-- **Lemma 21 (Final searches).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.22 (PDF 23).
"Let E3 be the event that, for every update t and every cut in K_t, some final cutset instance has a
sampling threshold that selects exactly one edge of the cut. Let E4 be the event that the fingerprint
test is sound for every update t, every cut in K_t, every final cutset instance, and every sampling
threshold. … Then Pr[not E3] ≤ T0 2^h (7/8)^r, Pr[not E4] ≤ T0 2^h r(J + 1)2^{J−w}."

**Formalization Note.** The sequence is fixed in advance, valid, with at most `T0` updates. -/
theorem lemma_21 {n : ℕ} (hn : 2 ≤ n) (S : AlgSetup n) (hS : S.Wf)
    (σ : List (PunctSketch.Update n)) (hσ : PunctSketch.IsValidStream σ) (T0 : ℕ)
    (hT0 : σ.length ≤ T0) :
    probR S {R | ¬ E3 S R σ} ≤ (T0 : ℝ) * 2 ^ hpar S * (7 / 8 : ℝ) ^ S.r ∧
    probR S {R | ¬ E4 S R σ} ≤
      (T0 : ℝ) * 2 ^ hpar S * S.r * (Jbits n + 1) * (2 : ℝ) ^ ((Jbits n : ℤ) - S.w) := by sorry

end DynConnWC
