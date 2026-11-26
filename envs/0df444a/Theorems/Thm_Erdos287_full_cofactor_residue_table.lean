-- Prove2me | Theorems.Thm_Erdos287_full_cofactor_residue_table
-- name    : Erdos287.full_cofactor_residue_table
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-26T11:53:17.024208+00:00
-- url     : https://prove2.me/theorems/80887d37-b56e-578e-a568-de5614417d3f
-- title:
--   Exact finite translation table using the full cofactor carry
-- statement:
--   For prime $p$ and a finite family of cofactor patterns of diameter less than $p^{h+1}$, set $P=p^{2h+1}$. Each nonempty selected pattern in a positive denominator set of reciprocal sum one has its translation in a finite set of classes modulo $P$. The set is given exactly by testing, at the positive representative $c=z+P$, whether some nonempty pattern has its cleared numerator divisible by $p^{v_p(L)+1}$, where $L$ is the product of its cofactors.
-- source:
--   Erdős Problem 287, https://www.erdosproblems.com/287.

import Mathlib

theorem Erdos287.full_cofactor_residue_table (p h : ℕ) (hp : p.Prime) (F : Finset (Finset ℕ))
    (hwidth : ∀ T ∈ F, ∀ a ∈ T, ∀ b ∈ T, a < b + p ^ (h + 1)) :
    let P := p ^ (2 * h + 1)
    ∃ R : Finset (ZMod P),
      (∀ z : ZMod P, z ∈ R ↔ ∃ T ∈ F, T.Nonempty ∧
        let c := z.val + P
        let L := ∏ d ∈ T, (c + d)
        p ^ (padicValNat p L + 1) ∣ ∑ i ∈ T, ∏ d ∈ T.erase i, (c + d)) ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        ∀ T ∈ F,
          T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
          T.Nonempty → (c : ZMod P) ∈ R := by sorry
