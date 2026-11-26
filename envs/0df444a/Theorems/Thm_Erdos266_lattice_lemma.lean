-- Prove2me | Theorems.Thm_Erdos266_lattice_lemma
-- name    : Erdos266.lattice_lemma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:42:23.270227+00:00
-- url     : https://prove2.me/theorems/7b01f715-697b-4bf8-8a5a-834cc33bb42d
-- title:
--   Erdos266: lattice lemma
-- statement:
--   **Lemma 7.2 of [KoTa24]** with existential constants: one block of `d`
--   shifted samples steers all `d` first coordinates of the running sums into
--   any target within the `ε`-box, up to the `D`-error box.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L150-L415
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L150-L415

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix
set_option maxHeartbeats 3200000

theorem Erdos266.lattice_lemma (d : ℕ) :
    ∃ ε D : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 1 ≤ D ∧
      ∀ (N M : ℕ), 1 ≤ N → 4 * d * M ≤ N →
      ∀ x : Fin d → ℝ,
        (∀ i : Fin d, |x i - ∑ j : Fin d, f (i.val + 1) (((j.val + 1) * N : ℕ) : ℝ)|
          ≤ ε * M / (N : ℝ) ^ (i.val + 2)) →
        ∃ n : Fin d → ℤ, (∀ j, |n j| ≤ (M : ℤ)) ∧
          ∀ i : Fin d,
            |x i - ∑ j : Fin d, f (i.val + 1) ((((j.val + 1) * N : ℕ) : ℝ) + (n j : ℝ))|
              ≤ D * (1 / (N : ℝ) ^ (i.val + 2) + (M : ℝ) ^ 2 / (N : ℝ) ^ (i.val + 3)) := by sorry
