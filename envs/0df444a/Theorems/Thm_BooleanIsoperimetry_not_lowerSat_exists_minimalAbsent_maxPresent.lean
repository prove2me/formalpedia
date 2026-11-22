-- Prove2me | Theorems.Thm_BooleanIsoperimetry_not_lowerSat_exists_minimalAbsent_maxPresent
-- name    : BooleanIsoperimetry.not_lowerSat_exists_minimalAbsent_maxPresent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:25:17.439294+00:00
-- url     : https://prove2.me/theorems/a20ed6a6-61fc-4988-8cf9-4f1e81e3d3fc
-- title:
--   Boolean Isoperimetry: not lower Sat exists minimal Absent max Present
-- statement:
--   **Extremal witness selection for lower-saturation failure (proved).**
--
--   If `A` is not lower-level-saturated, there is a `⊆`-minimal absent block `T`
--   (every proper subset of `T` lies in `A`) together with a maximum-cardinality
--   present block `S`, and `T.card < S.card`.  This is the honest, dimension-free
--   *selection* half of the Frankl–Füredi level-terminalization step; it needs only
--   failure of saturation, not down-fixedness.
--
--   It does **not** by itself give an admissible block: the finite checker
--   `verify_nearMiss_false_small.py` shows (claim `UA`, N = 5) that not every such
--   extremal pair is jointly admissible, so the eventual proof of
--   `downFixed_not_lowerSat_exists_admissibleBlock` must still select *which* extremal
--   pair works.  But every candidate produced here is a genuine minimal-absent /
--   max-present witness, exactly the objects the paper move ranges over.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1447-L1478
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BooleanIsoperimetry/Compression.lean#L1447-L1478

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

theorem BooleanIsoperimetry.not_lowerSat_exists_minimalAbsent_maxPresent {N : ℕ} {A : Finset (Cube N)}
    (h : ¬ IsLowerLevelSaturated A) :
    ∃ (T S : Cube N), T ∉ A ∧ (∀ R : Cube N, R ⊂ T → R ∈ A) ∧
      S ∈ A ∧ (∀ R ∈ A, R.card ≤ S.card) ∧ T.card < S.card := by sorry
