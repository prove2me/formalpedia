-- Prove2me | Theorems.Thm_BSLambda_LLL_card_le_three_of_good
-- name    : BSLambda.LLL.card_le_three_of_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:09:01.478814+00:00
-- url     : https://prove2.me/theorems/5117625f-ece1-4eaa-9067-f8de91e3263b
-- title:
--   LLL: card le three of good
-- statement:
--   **(L1)** (Section 10.3): a positive point has at most three other certificates at
--   distance one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L854-L860
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L854-L860

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}

theorem BSLambda.LLL.card_le_three_of_good (hT : IsTournament Arc) {ω : GateCfg ι r}
    (hgood : ∀ i : BadIdx Arc, ω ∉ badEvent Arc i) (h : ι)
    (x : Input (Coord ι r)) (hx : (cert Arc (toGamma ω) h).Sat x) :
    (Finset.univ.filter fun j =>
        j ≠ h ∧ (cert Arc (toGamma ω) j).dist x = 1).card ≤ 3 := by sorry
