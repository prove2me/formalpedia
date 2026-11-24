-- Prove2me | Theorems.Thm_BSLambda_Construction_filter_conflict_eq_singleton
-- name    : BSLambda.Construction.filter_conflict_eq_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:56:51.674029+00:00
-- url     : https://prove2.me/theorems/1ed8f719-acf2-4d14-8038-8d5dddea273d
-- title:
--   Construction: filter conflict eq singleton
-- statement:
--   The set of coordinates on which `C_i` and `C_j` conflict is the singleton `{q_{ij}}`
--   (Section 4).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L91-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Construction/Conflict.lean#L91-L99

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Conflict
set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.Construction
variable {ι : Type*} {r : ℕ}
variable [Fintype ι] [DecidableEq ι] {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i j : ι}

theorem BSLambda.Construction.filter_conflict_eq_singleton (hT : IsTournament Arc)
    (hji : j ≠ i) (hij : Arc i j) :
    (Finset.univ.filter fun v : Coord ι r ↦ (cert Arc γ i).Conflict (cert Arc γ j) v)
      = {gateCoord γ i j} := by sorry
