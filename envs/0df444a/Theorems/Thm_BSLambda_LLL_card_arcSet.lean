-- Prove2me | Theorems.Thm_BSLambda_LLL_card_arcSet
-- name    : BSLambda.LLL.card_arcSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:21.634103+00:00
-- url     : https://prove2.me/theorems/8478e778-1591-473e-b212-c5a648ef2b3a
-- title:
--   LLL: card arc Set
-- statement:
--   A tournament on `T` has exactly `C(|T|, 2)` internal arcs: six for the four non-owners
--   of a radius-one flag, and `Q = 28` for the eight non-owners of Section 9.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L143-L152
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L143-L152

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
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}
variable (hT : IsTournament Arc)
include hT
omit [DecidableEq ι]

theorem BSLambda.LLL.card_arcSet (T : Finset ι) : (arcSet Arc T).card = Nat.choose T.card 2 := by sorry
