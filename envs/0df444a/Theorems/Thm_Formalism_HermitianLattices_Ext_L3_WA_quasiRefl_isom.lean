-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_quasiRefl_isom
-- name    : Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_isom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:50.972195+00:00
-- url     : https://prove2.me/theorems/f1891815-5fd3-494c-8efe-0c6e50f30433
-- title:
--   WA: quasi Refl isom
-- statement:
--   The WA construction uses the quasi Refl isom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFix.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomFix.lean#L29-L38

import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.WA.quasiRefl_isom {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (u : V) {a : K}
    (ha : a + star a = a * star a * h u u) (v w : V) :
    h (quasiRefl h u a v) (quasiRefl h u a w) = h v w := by sorry
