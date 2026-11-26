-- Prove2me | Theorems.Thm_Auto_shortlongJumps
-- name    : Auto.shortlongJumps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:56:26.963282+00:00
-- url     : https://prove2.me/theorems/e129be85-9a05-4093-9adc-94bd6d7f9143
-- title:
--   Auto: shortlong Jumps
-- statement:
--   **Lemma.**
--
--   For every increasing sequence of positive real numbers $(t_j)_{j\in[J+1)}$,
--
--   $$
--   \Big(\sum_{j\in[J)}\|a(t_{j+1})-a(t_j)\|^r\Big)^{1/r}
--   \le
--   2\Big(\sum_{k\in\kappa}\|a\|_{V_{r,J}([2^k,2^{k+1}];B)}^r\Big)^{1/r}
--   +\|a\|_{V_{r,J}(2^\mathbb{Z};B)},
--   $$
--
--   where $\kappa$ is the set of $k\in\mathbb{Z}$ such that $2^k\le t_j<2^{k+1}$ for some $j\in[J+1)$.
--   Consequently,
--
--   $$
--   \|a\|_{V_{r,J}((0,\infty);B)}
--   \le
--   2\Big(\sum_{k\in\mathbb{Z}}\|a\|_{V_{r,J}([2^k,2^{k+1}];B)}^r\Big)^{1/r}
--   +\|a\|_{V_{r,J}(2^\mathbb{Z};B)}.
--   $$
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L372-L580
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/Reduction/VariationSeminorms.lean#L372-L580

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_Reduction_VariationSeminorms
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem Auto.shortlongJumps {B : Type*} [SeminormedAddCommGroup B]
    (a : ℝ → B) (J : ℕ) (r : ℝ) (hr : 1 ≤ r) :
    (∀ (t : Fin (J + 1) → ℝ), Monotone t → (∀ j, 0 < t j) →
      ∃ κ : Finset ℤ,
        (∀ k, k ∈ κ ↔ ∃ j, (2 : ℝ) ^ k ≤ t j ∧ t j < (2 : ℝ) ^ (k + 1)) ∧
        (∑ j : Fin J,
          (‖a (t j.succ) - a (t j.castSucc)‖₊ : ℝ≥0∞) ^ r) ^ r⁻¹ ≤
          2 * (∑ k ∈ κ,
            (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
          finiteVariationSeminorm
            (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J) ∧
    finiteVariationSeminorm (fun s : Set.Ioi (0 : ℝ) ↦ a s) r J ≤
      2 * (∑' k : ℤ,
        (finiteVariationSeminorm (fun s : aux_dyadicInterval k ↦ a s) r J) ^ r) ^ r⁻¹ +
      finiteVariationSeminorm
        (fun s : Set.range (fun k : ℤ ↦ (2 : ℝ) ^ k) ↦ a s) r J := by sorry
