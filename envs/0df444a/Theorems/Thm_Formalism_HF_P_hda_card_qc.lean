-- Prove2me | Theorems.Thm_Formalism_HF_P_hda_card_qc
-- name    : Formalism.HF.P.hda_card_qc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:28.173804+00:00
-- url     : https://prove2.me/theorems/43455d1a-92ae-44aa-afc8-1a5d8e262b4d
-- title:
--   P: hda card qc
-- statement:
--   The P construction uses the hda card qc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L21-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DirichletDensity/DirichletDensityProofs/HostDensityArith.lean#L21-L51

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P

theorem Formalism.HF.P.hda_card_qc (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (e : ℤ) (he : e = 1 ∨ e = -1) :
    2 * (univ.filter (fun y : ZMod p => quadraticChar (ZMod p) y = e)).card = p - 1 := by sorry
