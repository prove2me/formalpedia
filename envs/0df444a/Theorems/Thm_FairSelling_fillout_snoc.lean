-- Prove2me | Theorems.Thm_FairSelling_fillout_snoc
-- name    : FairSelling.fillout_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:44.369664+00:00
-- url     : https://prove2.me/theorems/420fa7f1-5225-4478-8ce8-76a258e743fb
-- title:
--   Fair Selling: fillout snoc
-- statement:
--   Adding one more part, of index `m`, on top of a filling of the smaller state.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L84-L256
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L84-L256

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.fillout_snoc (w p : G → ℝ) (ε : ℝ) {m : ℕ}
    {Res Res' : Finset G} {d r d' r' : ℝ} {f₀ f₀' : Option G}
    (F : FillOut w p ε m Res' d' r' f₀') (hRes' : Res' ⊆ Res)
    (hf₀' : ∀ f, f₀' = some f → f ∈ Res ∪ f₀.toFinset)
    (Enew : Finset G) (srcnew : Option G) (dnew snew : ℝ)
    (hEnew : Enew ⊆ Res)
    (hEdisj : Disjoint Enew (Res' ∪ f₀'.toFinset ∪ srcnew.toFinset))
    (hdnew : 0 ≤ dnew) (hsnew : 0 ≤ snew) (hd : d' + dnew ≤ d)
    (hacc : 2 * ε ≤ vbarSum w p Enew + dnew + snew)
    (hps : srcnew = none ∨ ∃ e, Enew = {e})
    (hsd : srcnew ≠ none → dnew = 0)
    (hsl : srcnew ≠ none → ∀ e ∈ Enew, ε ≤ vbar w p e)
    (hsz : srcnew = none → snew = 0)
    (hsnotin : ∀ f, srcnew = some f → f ∉ Res' ∧ ε ≤ p f ∧ f ∈ Res ∪ f₀.toFinset)
    (hmoney : ∀ f, (if srcnew = some f then snew else 0)
      + (if f ∈ F.sell then (if f₀' = some f then r' else p f) else 0)
      ≤ (if f₀ = some f then r else p f)) :
    Nonempty (FillOut w p ε (m + 1) Res d r f₀) := by sorry
