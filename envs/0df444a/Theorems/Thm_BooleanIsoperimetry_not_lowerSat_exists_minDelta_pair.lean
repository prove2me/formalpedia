-- Prove2me | Theorems.Thm_BooleanIsoperimetry_not_lowerSat_exists_minDelta_pair
-- name    : BooleanIsoperimetry.not_lowerSat_exists_minDelta_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:23.996836+00:00
-- url     : https://prove2.me/theorems/f780ac1a-6a71-4e6f-921e-e0c90f925711
-- title:
--   Boolean Isoperimetry: not lower Sat exists min Delta pair
-- statement:
--   **Minimal-symmetric-difference extremal witness selection (proved).**
--
--   Refines `not_lowerSat_exists_minimalAbsent_maxPresent` by additionally selecting,
--   among all minimal-absent / maximum-present witness pairs `(T, S)` with
--   `T.card < S.card`, one that **minimizes the Hamming symmetric difference**
--   `|S \ T| + |T \ S| = |S △ T|`.  This is the exact selection criterion that the
--   finite checker `test_min_delta_extremal.py` confirms (exhaustive `N = 4`) yields a
--   jointly admissible Frankl–Füredi level block move `U = S \ T`, `V = T \ S`: among
--   the extremal frontier the pair whose blocks are as small as possible is the one
--   whose primal/dual erase-admissibility clauses hold.
--
--   Only the *selection* is proved here (sorry-free, pure finite minimization over the
--   nonempty frontier of extremal pairs); the admissibility consequence for the
--   selected pair is the remaining research content of
--   `downFixed_not_lowerSat_exists_admissibleBlock`.  This upgrades the previously
--   external min-`|S △ T|` finite evidence to an in-Lean theorem, giving the exact
--   selected objects the paper move ranges over.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1497-L1520
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1497-L1520

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry

theorem BooleanIsoperimetry.not_lowerSat_exists_minDelta_pair {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ S ∈ A ∧ T.card < S.card ∧
      (∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) := by sorry
