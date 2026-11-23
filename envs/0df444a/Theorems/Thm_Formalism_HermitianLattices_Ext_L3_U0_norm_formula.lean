-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_norm_formula
-- name    : Formalism.HermitianLattices.Ext.L3.U0.norm_formula
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:58.297798+00:00
-- url     : https://prove2.me/theorems/2073c766-e4cc-4699-90e8-85929fbc0cce
-- title:
--   U0: norm formula
-- statement:
--   The U0 construction uses the norm formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormRepresentation.lean#L161-L169

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
variable {V : Type*} [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.U0.norm_formula {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {y w : V} {a u ρ : K}
    (hy : h y y = star a * a * u) (hu : star u = u)
    (hρ : ρ * (h w y - u * a) + star (ρ * (h w y - u * a)) = u - h w w) :
    h (ρ • y + w) (ρ • y + w) = u * (star (1 + ρ * a) * (1 + ρ * a)) := by sorry
