-- Prove2me | Theorems.Thm_EvasivePatterns_proposition_2_1
-- name    : EvasivePatterns.proposition_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:20.259768+00:00
-- url     : https://prove2.me/theorems/46e50fc9-6e53-4c0f-ae38-88dd275b3d3c
-- title:
--   Proposition 2.1 — shape of a period support: $S_P=\{0,p,\dots,kp\}\cup E$ with a short tail $E$
-- statement:
--   Let $P$ be a nonempty word of length $m$ over any alphabet, with smallest period $p$, and write $m = kp + r$ with $k \ge 1$ and $0 \le r < p$. Then
--   $$
--   S_P := \{0\} \cup \mathrm{Per}(P) = I \cup E, \qquad I = \{0, p, \dots, kp\}, \qquad E \subseteq (\max\{p, m-p\}, m], \qquad E \cap p\mathbb Z = \varnothing,
--   $$
--   and the points of $E$ have pairwise distinct (nonzero) residues modulo $p$.
--
--   So the overlap shifts of a word form an evenly spaced grid followed by a short tail near the end. This is the shape to which the rigidity theorem (Theorem 3.1) and the primitive-Wronskian lemma (Lemma 5.1) apply.
--
--   Differences from the source:
--   - encoding: m = kp + r, where k ≥ 1 and 0 ≤ r < p → k = m / p and r = m % p, with 1 ≤ k and r < p as conclusions; reason: k and r are determined by m and p; the two clauses state that the division has the printed shape
--   - encoding: word of length m with smallest period p → P ≠ [] and p = minPeriod P; reason: a smallest period exists exactly for nonempty words; the condition only excludes the case where p is undefined
--   - encoding: the points of E have distinct nonzero residues modulo p → e ↦ e % p injective on E (nonzero residues are the clause E ∩ pℤ = ∅); reason: same content
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), Proposition 2.1, display (3), p.3 (PDF p.4), lines 75–77

import Mathlib
import Definitions.Def_EvasivePatterns_periods

namespace EvasivePatterns

/-- **Proposition 2.1 (Shape of a period support).** Let `P` be a word of length `m` with smallest
period `p`. Write `m = kp + r`, where `k ≥ 1` and `0 ≤ r < p`. Then
`S_P := {0} ∪ Per(P) = I ∪ E`, `I = {0, p, …, kp}`, `E ⊆ (max{p, m − p}, m]`, `E ∩ pℤ = ∅` (3).
The points of `E` have distinct nonzero residues modulo `p`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), Proposition 2.1, display (3), printed p. 3 (PDF p. 4), lines 75–77.

**Formalization Note** The word is a nonempty list over any alphabet with decidable equality;
`p = minPeriod P`, `k = m / p`, `r = m % p`, so the clauses `1 ≤ k` and `r < p` state that this
division has the printed shape. `I` is the image of `{0, …, k}` under `j ↦ j p`. "Distinct
residues" is injectivity of `e ↦ e % p` on `E`; "nonzero" is `E ∩ pℤ = ∅`. -/
theorem proposition_2_1 {α : Type*} [DecidableEq α] (P : List α) (hP : P ≠ []) :
    1 ≤ P.length / minPeriod P ∧ P.length % minPeriod P < minPeriod P ∧
    ∃ E : Finset ℕ,
      periodSupport P =
          (Finset.range (P.length / minPeriod P + 1)).image (fun j => j * minPeriod P) ∪ E ∧
        (∀ e ∈ E, max (minPeriod P) (P.length - minPeriod P) < e ∧ e ≤ P.length) ∧
        (∀ e ∈ E, ¬ minPeriod P ∣ e) ∧
        Set.InjOn (fun e => e % minPeriod P) (E : Set ℕ) := by sorry

end EvasivePatterns
