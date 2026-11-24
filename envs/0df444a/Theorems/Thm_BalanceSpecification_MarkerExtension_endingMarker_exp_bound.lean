-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_endingMarker_exp_bound
-- name    : BalanceSpecification.MarkerExtension.endingMarker_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:08.321491+00:00
-- url     : https://prove2.me/theorems/bd167fa0-946b-414e-a8fc-a22bef43f806
-- title:
--   Marker Extension: ending Marker exp bound
-- statement:
--   Common-tail suffix control and finite-generator growth control give the
--   strictly slower exponential envelope for words ending at a marker.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L123-L151
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L123-L151

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A]

theorem BalanceSpecification.MarkerExtension.endingMarker_exp_bound {hY : Y.carrier.Nonempty} {C ρ : ℝ}
    (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s) (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n)
    (hρ : Real.exp (entropy Y hY / 4) < ρ)
    (hgen : ∀ n : ℕ, (wordCount (generatedWords (code M hM x s)) n : ℝ) ≤ ρ ^ n)
    (n : ℕ) :
    ((endingMarkerFinset (shift M hM x s) (n + 1)).card : ℝ) ≤
      (C / (1 - Real.exp (entropy Y hY / 4) / ρ)) * ρ ^ n := by sorry
