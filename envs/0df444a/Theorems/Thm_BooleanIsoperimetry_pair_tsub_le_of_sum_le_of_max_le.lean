-- Prove2me | Theorems.Thm_BooleanIsoperimetry_pair_tsub_le_of_sum_le_of_max_le
-- name    : BooleanIsoperimetry.pair_tsub_le_of_sum_le_of_max_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:33:25.383311+00:00
-- url     : https://prove2.me/theorems/e17e7f97-f521-44d6-8604-09e353d169f7
-- title:
--   Boolean Isoperimetry: pair tsub le of sum le of max le
-- statement:
--   **Hardy–Littlewood–Pólya pair majorization for truncated (`ℕ`) tails.**
--
--   For two `ℕ`-pairs, if the pair `(a', b')` weakly majorizes `(a, b)` — i.e. the
--   sums satisfy `a + b ≤ a' + b'` *and* the maxima satisfy `max a b ≤ max a' b'` —
--   then every truncated-tail pair sum is dominated:
--   `(a - c) + (b - c) ≤ (a' - c) + (b' - c)` for all thresholds `c` (`ℕ` truncated
--   subtraction).  This is the two-point Hardy–Littlewood–Pólya / Karamata fact for
--   the increasing convex family `x ↦ (x - c)⁺`, specialised to a pair; it is the
--   *final pair-combination step* of any Macaulay upper-tail argument once the two
--   neighborhood-slice values have been compared.
--
--   Caveat (recorded so it is not misused).  The two hypotheses are **strictly
--   stronger** than what the cascade tail leaf `cascade_KK_tail_min` actually needs:
--   that leaf only requires the truncated inequality at the *Macaulay grid points*
--   `c = binomPrefix N k`, and the max-slice hypothesis `max a b ≤ max a' b'` is
--   **not** available there — it is verified false on genuine cascade configurations
--   (smallest witness `N = 3, a = b = 2`, neighborhood slices `(7,4)` vs `(6,6)`; see
--   `verify_cascade_KK_tail_weakMaj_insufficient_small.py`).  Hence this lemma is a
--   *sound but incomplete* tool for that leaf: it closes the tail only in the
--   weak-majorized regime, and the genuine remaining content lives in the grid
--   structure of `H`, to be handled by the dimension recursion `H_succ_cascade` and
--   the single-layer minimum `layerWindowShadowCost_KK_min`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L367-L370
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/LayerWindows.lean#L367-L370

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
set_option autoImplicit true
@[expose] public section
public section
open BooleanIsoperimetry
open Finset

theorem BooleanIsoperimetry.pair_tsub_le_of_sum_le_of_max_le {a b a' b' c : ℕ}
    (hsum : a + b ≤ a' + b') (hmax : max a b ≤ max a' b') :
    (a - c) + (b - c) ≤ (a' - c) + (b' - c) := by sorry
