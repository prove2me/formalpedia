-- Prove2me | Theorems.Thm_BSLambda_LLL_mem_branch2
-- name    : BSLambda.LLL.mem_branch2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:03:28.26333+00:00
-- url     : https://prove2.me/theorems/a927e71c-d0f5-4461-a48f-4ee4efe4cd50
-- title:
--   LLL: mem branch2
-- statement:
--   The LLL construction uses the mem branch2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L888-L893
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Obstruction.lean#L888-L893

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

theorem BSLambda.LLL.mem_branch2 {Arc : ι → ι → Bool} {S : Finset ι} {h : ι} {L : Finset ι}
    {w : (j : ι) → j ∈ L → Fin r} {X : Finset (ι × ι)} {ω : GateCfg ι r} :
    ω ∈ branch2 Arc S h L w X ↔ ∀ p ∈ arcSet Arc (S.erase h), p ∉ X →
      ω p = ω (h, p.2) ∨ ω p = (if hp : p.2 ∈ L then w p.2 hp else ω (h, p.2)) := by sorry
