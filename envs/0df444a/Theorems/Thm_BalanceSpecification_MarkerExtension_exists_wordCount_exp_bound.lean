-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_wordCount_exp_bound
-- name    : BalanceSpecification.MarkerExtension.exists_wordCount_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:19.903481+00:00
-- url     : https://prove2.me/theorems/4b2702de-3b29-490c-84c6-ebcc904b3b20
-- title:
--   Marker Extension: exists word Count exp bound
-- statement:
--   The two genuine boundary partitions yield a uniform source-entropy
--   exponential upper bound. All construction estimates are explicit helper inputs;
--   the source existence theorem must supply them from its sparse code.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L157-L223
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L157-L223

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

theorem BalanceSpecification.MarkerExtension.exists_wordCount_exp_bound {hY : Y.carrier.Nonempty} {C ρ : ℝ}
    (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s) (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n)
    (hρlo : Real.exp (entropy Y hY / 4) < ρ) (hρhi : ρ < Real.exp (entropy Y hY))
    (hgen : ∀ n : ℕ, (wordCount (generatedWords (code M hM x s)) n : ℝ) ≤ ρ ^ n) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (wordCount (language (shift M hM x s)) n : ℝ) ≤
      K * Real.exp ((n : ℝ) * entropy Y hY) := by sorry
