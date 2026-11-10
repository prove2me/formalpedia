-- Prove2me | Theorems.Thm_EvasivePatterns_lemma_a_2
-- name    : EvasivePatterns.lemma_a_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:15.477329+00:00
-- url     : https://prove2.me/theorems/0dea5e46-fd12-46eb-a1b7-569d38ea27f1
-- title:
--   Lemma A.2 — completion of a full progression: $T=S$ or $T=m-S$
-- statement:
--   Let $p, k, r, m$ be natural numbers with $k \ge 2$, $m = kp + r$ and $0 \le r < p$, let $E \subseteq (m - p, m]$ be a finite set of integers containing no multiple of $p$, and let
--   $$
--   S = \{0, p, \dots, kp\} \cup E .
--   $$
--   If a normalized homometric mate $T$ of $S$ ($\min T = 0$, $\max T = m$, $\mathcal D(T) = \mathcal D(S)$) contains $k + 1$ points in arithmetic progression with difference $p$, then $T = S$ or $T = m - S$.
--
--   These are the standing hypotheses of Appendix A for $k \ge 2$. The lemma completes the proof of Theorem 3.1 once a full grid has been found in the mate.
--
--   Differences from the source:
--   - encoding: k + 1 points in arithmetic progression with difference p → a, a + p, …, a + kp ∈ T for some integer a; reason: same content
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Appendix A.2, Lemma A.2, p.12 (PDF p.13), lines 385–386; standing hypotheses, p.11 (PDF p.12), lines 352–355

import Mathlib
import Definitions.Def_EvasivePatterns_distMultiset

namespace EvasivePatterns

/-- **Lemma A.2 (Completion of a full progression).** Let `S = I ∪ E`, `I = {0, p, …, kp}`,
`m = kp + r`, `0 ≤ r < p`, `E ⊆ (m − p, m]`, `E ∩ pℤ = ∅` (the standing hypotheses of Appendix A).
For `k ≥ 2`, if a normalized homometric mate `T` of `S` contains `k + 1` points in arithmetic
progression with difference `p`, then `T = S` or `T = m − S`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Appendix A.2, Lemma A.2, printed p. 12 (PDF p. 13), lines 385–386; standing
hypotheses of Appendix A, printed p. 11 (PDF p. 12), lines 352–355.

**Formalization Note** `p, k, r, m` are natural numbers (`p ≥ 1` follows from `r < p`), `E` and
`T` finite integer sets. A normalized homometric mate has `min T = 0`, `max T = m` and
`D(T) = D(S)`. The progression is `a, a + p, …, a + kp` for some integer `a`. `m − S` is the image
of `S` under `x ↦ m − x`. -/
theorem lemma_a_2 (p k r m : ℕ) (hk : 2 ≤ k) (hr : r < p) (hm : m = k * p + r)
    (E : Finset ℤ) (hE : ∀ e ∈ E, (m : ℤ) - p < e ∧ e ≤ m) (hEp : ∀ e ∈ E, ¬ (p : ℤ) ∣ e)
    (S : Finset ℤ) (hS : S = (Finset.range (k + 1)).image (fun j : ℕ => ((j * p : ℕ) : ℤ)) ∪ E)
    (T : Finset ℤ) (hTmin : T.min = (0 : WithTop ℤ)) (hTmax : T.max = (m : WithBot ℤ))
    (hTS : distMultiset T = distMultiset S)
    (hprog : ∃ a : ℤ, ∀ j : ℕ, j ≤ k → a + (j : ℤ) * p ∈ T) :
    T = S ∨ T = S.image (fun x => (m : ℤ) - x) := by sorry

end EvasivePatterns
