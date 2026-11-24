-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_orth_tuple
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_orth_tuple
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:07.414477+00:00
-- url     : https://prove2.me/theorems/b34a5177-d73f-448b-be89-f1c555b14926
-- title:
--   U0: exists orth tuple
-- statement:
--   The U0 construction uses the exists orth tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTuple.lean#L148-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsOrthTuple.lean#L148-L236

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

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_orth_tuple (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm) :
    ∀ (n : ℕ) (x : Fin n → V), (∀ i j, h (x i) (x j) ∈ S) →
      ¬ Dv S π ((gram h x).det * π⁻¹) →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by sorry
