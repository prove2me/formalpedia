-- Prove2me | Theorems.Thm_Erdos287_consecutive_omissions_from_multi_premise_residue_rules
-- name    : Erdos287.consecutive_omissions_from_multi_premise_residue_rules
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T07:06:50.701731+00:00
-- url     : https://prove2.me/theorems/1dd41469-2a61-4b6d-8db8-321ebe2a8ce6
-- title:
--   Rules with simultaneous antecedents certify consecutive omitted denominators
-- statement:
--   Let $D\subseteq[m,M]$ be positive distinct denominators with reciprocal sum one and common multiple $C$. A rule implies a keep/omit literal from a finite set of simultaneous literals. A rule can follow from spacing, fixed omitted or retained positions, or a local subset check. In the local check one may use the zero weighted sum modulo $q\mid C$, or the empty-layer alternative and minimum size bound for an exact highest $p$-valuation layer. If a finite sequence of applicable rules yields conflicting literals starting from either status of one position, two consecutive integers in $[m,M]$ are absent from $D$.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287. Finite local deductions using simultaneous antecedents and highest-layer size information.

import Mathlib

theorem Erdos287.consecutive_omissions_from_multi_premise_residue_rules (D H R : Finset ℕ) (m M C : ℕ)
    (hD : D ⊆ Finset.Icc m M) (hpos : ∀ n ∈ D, 0 < n)
    (hdiv : ∀ n ∈ D, n ∣ C) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (rule : Finset (ℕ × Bool) → (ℕ × Bool) → Prop)
    (hRules : ∀ A b, rule A b →
      (b.2 = true ∧
        ((b.1 - 1, false) ∈ A ∧ m < b.1 ∧ b.1 ≤ M ∨
         (b.1 + 1, false) ∈ A ∧ m ≤ b.1 ∧ b.1 + 1 ≤ M)) ∨
      (b.2 = true ∧ b.1 ∈ R) ∨ (b.2 = false ∧ b.1 ∈ H) ∨
      ∃ S : Finset ℕ, b.1 ∈ S ∧ (∀ a ∈ A, a.1 ∈ S) ∧
        ((∃ q : ℕ, q ∣ C ∧
          (∀ n ∈ Finset.Icc m M, ¬ q ∣ C / n → n ∈ S) ∧
          (∀ T ⊆ S, q ∣ (∑ n ∈ T, C / n) →
            (∀ a ∈ A, a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true))) ∨
         (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧
          (∀ n ∈ Finset.Icc m M, n ∉ H → padicValNat p n ≤ e ∧
            (n ∈ S ↔ padicValNat p n = e)) ∧
          (∀ T ⊆ S, (¬ T.Nonempty ∨ p ≤ T.card * (M / p ^ e) ^ (T.card - 1)) →
            (∀ a ∈ A, a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true)))))
    (hProof : ∃ root : ℕ, ∀ b : Bool, ∃ T : Finset (ℕ × Bool),
      Relation.ReflTransGen
        (fun X Y => ∃ A a, rule A a ∧ A ⊆ X ∧ Y = insert a X)
        {(root, b)} T ∧
      ∃ n, (n, true) ∈ T ∧ (n, false) ∈ T) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by sorry
