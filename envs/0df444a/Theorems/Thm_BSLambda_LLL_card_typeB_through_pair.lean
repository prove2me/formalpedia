-- Prove2me | Theorems.Thm_BSLambda_LLL_card_typeB_through_pair
-- name    : BSLambda.LLL.card_typeB_through_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:08:28.881685+00:00
-- url     : https://prove2.me/theorems/cc9e8a93-6dbf-4ab4-abea-77aab2fe019d
-- title:
--   LLL: card type B through pair
-- statement:
--   **Section 8.2**: at most `N_B = C(t,3) + 2 t C(t-1,2) + C(t,2)(t-2) = 71,519,595,000`
--   Type-B flags pass through the ordered pair `u → v`.  Of the nine possible pairs of roles for
--   `u` and `v`, two are impossible and three need the reverse arc `v → u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L574-L622
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/GateExists.lean#L574-L622

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
open scoped Classical

theorem BSLambda.LLL.card_typeB_through_pair (hT : IsDRTournamentWith Arc 7005 3502)
    {u v : ι} (huv : u ≠ v) (harc : Arc u v = true) :
    (Finset.univ.filter fun G : Flag1 ι =>
        G.Active Arc ∧ G.top ≠ none ∧ u ∈ G.supp ∧ v ∈ G.supp).card
      ≤ 71519595000 := by sorry
