-- Prove2me | Theorems.Thm_BSLambda_LLL_card_flags_le_mul_choose
-- name    : BSLambda.LLL.card_flags_le_mul_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:00:45.332812+00:00
-- url     : https://prove2.me/theorems/19dd8949-4860-494c-a274-34859ed5fc03
-- title:
--   LLL: card flags le mul choose
-- statement:
--   **The counting scheme behind all six flag counts of Section 8.2.**  An active flag is
--   determined by its head `(owner, top)` together with its bottom set, and the bottom set is a
--   `c`-element subset of the common out-neighbourhood of the head containing the forced vertices
--   `W`.  So if every flag satisfying `P` has its head in `H` and at most `N` unforced candidates
--   for the remaining `c - |W|` bottom vertices, there are at most `|H| * C(N, c - |W|)` of them.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L348-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L348-L383

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

theorem BSLambda.LLL.card_flags_le_mul_choose {P : Flag1 ι → Prop} [DecidablePred P]
    {H : Finset (ι × Option ι)} {W : Finset ι} {c N : ℕ}
    (hact : ∀ G, P G → G.Active Arc) (hhead : ∀ G, P G → (G.owner, G.top) ∈ H)
    (hW : ∀ G, P G → W ⊆ G.bot) (hbot : ∀ G, P G → G.bot.card = c)
    (hN : ∀ G, P G → (headOut Arc (G.owner, G.top) \ W).card ≤ N) :
    (Finset.univ.filter P).card ≤ H.card * Nat.choose N (c - W.card) := by sorry
