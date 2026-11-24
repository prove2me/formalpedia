-- Prove2me | Theorems.Thm_Formalism_L2_Pj_incG_mul
-- name    : Formalism.L2.Pj.incG_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:39.794473+00:00
-- url     : https://prove2.me/theorems/6a5507d1-3c9c-4759-a36e-6ba77f0304a7
-- title:
--   Pj: inc G mul
-- statement:
--   The Pj construction uses the inc G mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ErealAddIInf.lean#L50-L52

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ErealAddIInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K R M W : Type} [Field K] [CommRing R] [Algebra K R] [AddCommMonoid M] (key : W → M)
  (C : W → Submodule K R)

theorem Formalism.L2.Pj.incG_mul {w w' u : W} (hu : key u = key w + key w') (F : C w) (F' : C w')
    (h : (F : R) * (F' : R) ∈ C u) : incG key C w F * incG key C w' F' = incG key C u ⟨_, h⟩ := by sorry
