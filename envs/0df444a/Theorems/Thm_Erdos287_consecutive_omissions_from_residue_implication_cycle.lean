-- Prove2me | Theorems.Thm_Erdos287_consecutive_omissions_from_residue_implication_cycle
-- name    : Erdos287.consecutive_omissions_from_residue_implication_cycle
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T06:53:30.455531+00:00
-- url     : https://prove2.me/theorems/8e31866f-ef62-5ead-a680-15935d63b575
-- title:
--   Paths of local residue implications certify consecutive omitted denominators
-- statement:
--   Let $D\subseteq[m,M]$ be positive denominators with reciprocal sum one and common multiple $C$. Use literals for retaining or omitting a position. Each directed implication may come from the restriction on consecutive omissions, a known retained or omitted position, or a modular equation on a finite support. A modular implication modulo $q\mid C$ is valid if it holds for every subset of a support containing both literals' positions and all positions with $C/n\not\equiv0\pmod q$ whose weighted sum is zero modulo $q$. If there are paths from a literal to its opposite and back, two consecutive integers in $[m,M]$ are absent.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Local modular implication certificates combined through spacing constraints.

import Mathlib

theorem Erdos287.consecutive_omissions_from_residue_implication_cycle (D H R : Finset ℕ) (m M C : ℕ)
    (hD : D ⊆ Finset.Icc m M) (hpos : ∀ n ∈ D, 0 < n)
    (hdiv : ∀ n ∈ D, n ∣ C) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (edge : (ℕ × Bool) → (ℕ × Bool) → Prop)
    (hEdges : ∀ a b, edge a b →
      (a.2 = false ∧ b.2 = true ∧
        ((a.1 + 1 = b.1 ∧ m ≤ a.1 ∧ b.1 ≤ M) ∨
         (b.1 + 1 = a.1 ∧ m ≤ b.1 ∧ a.1 ≤ M))) ∨
      (b.2 = true ∧ b.1 ∈ R) ∨ (b.2 = false ∧ b.1 ∈ H) ∨
      ∃ (q : ℕ) (S : Finset ℕ), q ∣ C ∧ a.1 ∈ S ∧ b.1 ∈ S ∧
        (∀ n ∈ Finset.Icc m M, ¬ q ∣ C / n → n ∈ S) ∧
        (∀ T ⊆ S, q ∣ (∑ n ∈ T, C / n) →
          (a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true)))
    (hPaths : ∃ n, Relation.ReflTransGen edge (n, true) (n, false) ∧
      Relation.ReflTransGen edge (n, false) (n, true)) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by sorry
