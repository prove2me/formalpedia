-- Prove2me | Theorems.Thm_BSLambda_LLL_intObstruction_two_nonowner
-- name    : BSLambda.LLL.intObstruction_two_nonowner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:32.966564+00:00
-- url     : https://prove2.me/theorems/1d70205a-37c3-4e62-ad3e-2c6d53c07519
-- title:
--   LLL: int Obstruction two nonowner
-- statement:
--   **Section 9, budget at one non-owner.**  If `h → j` then `γ h j ∈ Z j`; if `j → h` then
--   the arc `j → h` is an automatic miss because `Z h = ∅`.  Either way `Z j` is contained in a
--   two-element set consisting of the owner gate and one discretionary zero, and `j` has at most
--   one further internal discrepancy, which it loses if it uses the discretionary zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L935-L980
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L935-L980

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

theorem BSLambda.LLL.intObstruction_two_nonowner [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j) {j : ι} (hj : j ∈ S.erase h)
    (hbud : (Z j).card + (missSet Arc γ Z S j).card ≤ 2) :
    (∃ z : Fin r, Z j ⊆ {γ h j, z}) ∧
      (missSet Arc γ Z (S.erase h) j).card + (if Z j ⊆ {γ h j} then 0 else 1) ≤ 1 := by sorry
