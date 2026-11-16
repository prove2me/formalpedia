-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_Supplement_theorem_2_3
-- name    : BirthdayEntropy.Soundness.Supplement.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:22:45.773214+00:00
-- url     : https://prove2.me/theorems/c88d0515-e899-4341-9ef0-fe92009a5804
-- title:
--   Theorem 2.3 — Unrestricted multi-answer agreement stability
-- statement:
--   Let $n\ge1$, $1\le\ell\le n$ and $K=\binom n\ell$. Let $H$ be any set of exactly $K$ distinct pairs $(S,a)$, with $|S|=\ell$ and $a:S\to\{0,1\}$. For independent uniform selected vertices sampled with replacement, let $q_{\rm con}(H)$ be the probability of any conflicting bit on their common coordinates. Let $A_g(H)$ count all views $S$ whose restriction $(S,g|_S)$ belongs to $H$, and $f^*(H)=1-\max_g A_g(H)/K$. Then
--
--   $$f^*(H)\le34\frac n\ell q_{\rm con}(H).$$
--
--   This companion theorem has no CSP or small-error hypothesis. It includes missing views, multiple answers, $q_{\rm con}=0$, $\ell=1$ and $\ell=n$. It is not used in the proof of Theorem 2.1; it also supports Theorem B.3.
--
--   Differences from the source:
--   - encoding: a set of K distinct Boolean labelled views → a Finset of published Vertex (Fin n coordinates) with card = choose n ell; reason: finite sets enforce distinctness and represent every source selection; normalization is unchanged
--   - encoding: maximum over all global assignments → sup' of the nonempty finite set of Boolean assignments; reason: a finite maximum is attained; there is no default empty or unbounded real supremum
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Theorem 2.3, PDF p4 / printed p3

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement

namespace BirthdayEntropy.Soundness.Supplement

/-- Theorem 2.3, PDF p4 / printed p3. Companion theorem; not used in the
proof of the goal. Full view range and arbitrary K-element vertex sets. -/
theorem theorem_2_3 (n ℓ : ℕ) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n)
    (H : Finset (Vertex n ℓ)) (hH : H.card = Nat.choose n ℓ) :
    fstar H ≤ 34 * ((n : ℝ) / ℓ) * qcon H := by sorry

end BirthdayEntropy.Soundness.Supplement
