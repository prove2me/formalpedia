-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_radiusTwoEvent
-- name    : BSLambda.LLL.mem_radiusTwoEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:01:46.030657+00:00
-- url     : https://prove2.me/theorems/ab8f54b4-97a5-4574-a6ee-00028e429003
-- title:
--   LLL: mem radius Two Event
-- statement:
--   Membership in the radius-two event.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L786-L788
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L786-L788

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

theorem BSLambda.LLL.mem_radiusTwoEvent {Arc : ι → ι → Bool} {S : Finset ι} {ω : GateCfg ι r} :
    ω ∈ radiusTwoEvent Arc S ↔ ∃ h ∈ S, IntObstruction Arc 2 S h (toGamma ω) := by sorry
