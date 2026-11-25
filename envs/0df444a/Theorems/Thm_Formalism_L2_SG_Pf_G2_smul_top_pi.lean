-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G2_smul_top_pi
-- name    : Formalism.L2.SG.Pf.G2.smul_top_pi
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:37.257925+00:00
-- url     : https://prove2.me/theorems/a18785e1-9dad-56a0-9bcc-9e186f2deac0
-- title:
--   G2: smul top pi
-- statement:
--   The G2 construction uses the smul top pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardQuotSmulTopCongr.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CardQuotSmulTopCongr.lean#L13-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsSubDivMemSP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardQuotSmulTopCongr
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3

theorem Formalism.L2.SG.Pf.G2.smul_top_pi {R : Type*} [CommRing R] {κ : Type*} [Fintype κ] [DecidableEq κ]
    {N : κ → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (J : Ideal R) :
    (J • ⊤ : Submodule R (∀ i, N i)) =
      Submodule.pi Set.univ (fun i => J • (⊤ : Submodule R (N i))) := by sorry
