-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_pivot
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_pivot
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:05:38.181525+00:00
-- url     : https://prove2.me/theorems/1f7c103e-ec92-4b02-ac2f-e2d9f96a20c6
-- title:
--   U0: exists pivot
-- statement:
--   The U0 construction uses the exists pivot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTuple.lean#L115-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTuple.lean#L115-L141

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanSInduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_pivot (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) {n : ℕ}
    (x : Fin (n + 1) → V) (hx : ∀ i j, h (x i) (x j) ∈ S)
    (hnd : ∃ i j, ¬ Dv S π (h (x i) (x j))) :
    ∃ i₀ : Fin (n + 1), ∃ r ∈ spanS S (x ∘ i₀.succAbove), IsUnitIn S (h (x i₀ + r) (x i₀ + r)) := by sorry
