-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_col
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.mem_col
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:15.558191+00:00
-- url     : https://prove2.me/theorems/175a3665-bc02-4d7f-938d-c2b89bd5dfb3
-- title:
--   Ball B: mem col
-- statement:
--   The Ball B construction uses the mem col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L30-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L30-L30

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.BallB.mem_col {I : Ideal (𝓞 K)} {z c : 𝓞 K} : c ∈ col I z ↔ c * z ∈ I := by sorry
