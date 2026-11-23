-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gnExt_mulVec
-- name    : Formalism.QuantumDeterminants.gnExt_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:03.655798+00:00
-- url     : https://prove2.me/theorems/87ec4dae-3952-4f3c-8a26-e3a3b1e9c308
-- title:
--   Quantum Determinants: gn Ext mul Vec
-- statement:
--   The Quantum Determinants construction uses the gn Ext mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L20-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L20-L35

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.gnExt_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (v : {i // p i} → ℂ) (i : ι) :
    (gnExt p *ᵥ v) i = if h : p i then v ⟨i, h⟩ else 0 := by sorry
