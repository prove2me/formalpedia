-- Prove2me | Theorems.Thm_BSLambda_LLL_card_arcSet_erase
-- name    : BSLambda.LLL.card_arcSet_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:33.480458+00:00
-- url     : https://prove2.me/theorems/f84144cb-143b-49f1-8c47-ca8dc675f18c
-- title:
--   LLL: card arc Set erase
-- statement:
--   The eight non-owners of a nine-element support span `Q = C(8, 2) = 28` internal arcs.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L915-L919
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L915-L919

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

theorem BSLambda.LLL.card_arcSet_erase {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι}
    (hh : h ∈ S) : (arcSet Arc (S.erase h)).card = 28 := by sorry
