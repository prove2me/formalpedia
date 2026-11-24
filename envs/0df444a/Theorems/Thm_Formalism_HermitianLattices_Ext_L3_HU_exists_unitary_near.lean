-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_exists_unitary_near
-- name    : Formalism.HermitianLattices.Ext.L3.HU.exists_unitary_near
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:18.23429+00:00
-- url     : https://prove2.me/theorems/1953b16a-1598-4091-89c0-ac2e7d0d0764
-- title:
--   HU: exists unitary near
-- statement:
--   The HU construction uses the exists unitary near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsUnitaryNear.lean#L12-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsUnitaryNear.lean#L12-L39

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StepIdentity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsInvOneAdd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsUnitaryNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.HermitianLattices.Ext.L3.HU.exists_unitary_near [CharZero K] (hS : IsLocUnif S ϖ) {H E : Matrix n n K} (hH : Hᴴ = H)
    (hHS : Ent S H) (hES : Ent S E) {e k : ℕ} (hHE : H * E = ϖ ^ e • (1 : Matrix n n K))
    (hk : e + 1 ≤ k) {X Z : Matrix n n K} (hX : Ent S X) (hZ : Ent S Z)
    (hXZ : Xᴴ * H * X = H + ϖ ^ k • Z) :
    ∃ G G' D : Matrix n n K, Ent S G ∧ Ent S G' ∧ Ent S D ∧ G * G' = 1 ∧ Gᴴ * H * G = H ∧
      G = X + ϖ ^ (k - e) • D := by sorry
