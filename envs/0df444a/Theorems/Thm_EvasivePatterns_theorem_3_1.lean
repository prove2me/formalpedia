-- Prove2me | Theorems.Thm_EvasivePatterns_theorem_3_1
-- name    : EvasivePatterns.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:39.243137+00:00
-- url     : https://prove2.me/theorems/a3caf8da-c090-43a8-80e7-7d282ff3472e
-- title:
--   Theorem 3.1 — a progression with a short terminal tail is homometrically rigid
-- statement:
--   Let $p, k \ge 1$, $m = kp + r$ with $0 \le r < p$, and
--   $$
--   S = \{0, p, \dots, kp\} \cup E, \qquad E \subseteq (\max\{p, m-p\}, m], \qquad E \cap p\mathbb Z = \varnothing, \qquad \max S = m,
--   $$
--   with $E$ a finite set of integers. Then $S$ is homometrically rigid: every set with the same distance multiset as $S$ is a translate of $S$ or of its reflection.
--
--   By Proposition 2.1 this applies to every period support $S_P$; it is the geometric heart of the argument.
--
--   Differences from the source:
--   - encoding: homometric sets (finite point sets) → nonempty finite integer sets (definition Rigid); reason: |S| ≥ 2, so every homometric set has at least two points; a real homometric set is an integer set up to translation
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Theorem 3.1, p.4 (PDF p.5), lines 133–134

import Mathlib
import Definitions.Def_EvasivePatterns_Rigid

namespace EvasivePatterns

/-- **Theorem 3.1 (Progression with a short terminal tail).** Let `p, k ≥ 1`, `m = kp + r`,
`0 ≤ r < p`, and `S = {0, p, …, kp} ∪ E`, `E ⊆ (max{p, m − p}, m]`, `E ∩ pℤ = ∅`, `max S = m`.
Then `S` is homometrically rigid.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Theorem 3.1, printed p. 4 (PDF p. 5), lines 133–134.

**Formalization Note** `p, k, r, m` are natural numbers, `E` and `S` finite integer sets;
`{0, p, …, kp}` is the image of `{0, …, k}` under `j ↦ j p`; `max S = m` uses `Finset.max`.
Rigidity (`Rigid`) is with respect to all nonempty finite integer sets. -/
theorem theorem_3_1 (p k r m : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (hr : r < p) (hm : m = k * p + r)
    (E : Finset ℤ) (hE : ∀ e ∈ E, max (p : ℤ) ((m : ℤ) - p) < e ∧ e ≤ m)
    (hEp : ∀ e ∈ E, ¬ (p : ℤ) ∣ e)
    (S : Finset ℤ) (hS : S = (Finset.range (k + 1)).image (fun j : ℕ => ((j * p : ℕ) : ℤ)) ∪ E)
    (hmax : S.max = (m : WithBot ℤ)) :
    Rigid S := by sorry

end EvasivePatterns
