-- Prove2me | Theorems.Thm_CriticalPortraits_beta_interval_closed
-- name    : CriticalPortraits.beta_interval_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:32.133957+00:00
-- url     : https://prove2.me/theorems/4a8ed8a8-849c-453e-98c2-3f477e7288b1
-- title:
--   Critical Portraits: beta interval closed
-- statement:
--   The Critical Portraits construction uses the beta interval closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1351-L1464
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1351-L1464

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.beta_interval_closed {d m : ℕ} (hd : 0 < d) (hm : 0 < m) {U : Finset (ZMod (d * m))}
    (hcanon : LevelCanonical d m U) {x z : ZMod (d * m)}
    (hx : x ∈ bVerts U) (hz : z ∈ bVerts U)
    (hne : betaBlock U x ≠ betaBlock U z)
    {p : ZMod (d * m)} (hp : p ∈ betaBlock U z)
    (hlo : (minVal (betaBlock U x) (betaBlock_nonempty hx)).val < p.val)
    (hhi : p.val < (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val) :
    ∀ q ∈ betaBlock U z, (minVal (betaBlock U x) (betaBlock_nonempty hx)).val ≤ q.val ∧
      q.val ≤ (maxVal (betaBlock U x) (betaBlock_nonempty hx)).val := by sorry
