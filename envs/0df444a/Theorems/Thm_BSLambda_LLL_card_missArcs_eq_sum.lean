-- Prove2me | Theorems.Thm_BSLambda_LLL_card_missArcs_eq_sum
-- name    : BSLambda.LLL.card_missArcs_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:07:27.073241+00:00
-- url     : https://prove2.me/theorems/298804e0-2fdb-4038-b87e-affcdc81edf5
-- title:
--   LLL: card miss Arcs eq sum
-- statement:
--   The missing arcs of `T` fibre over their tails, the fibre above `j` being the misses of
--   `j` inside `T`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L858-L873
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L858-L873

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}
omit [DecidableEq ι]

theorem BSLambda.LLL.card_missArcs_eq_sum (hT : IsTournament Arc) (T : Finset ι) :
    (missArcs Arc γ Z T).card = ∑ j ∈ T, (missSet Arc γ Z T j).card := by sorry
