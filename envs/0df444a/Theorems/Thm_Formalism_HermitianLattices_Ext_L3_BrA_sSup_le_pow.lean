-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_sSup_le_pow
-- name    : Formalism.HermitianLattices.Ext.L3.BrA.sSup_le_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:18.987143+00:00
-- url     : https://prove2.me/theorems/f63d7bbc-338e-4328-b05d-c3f75b4ee73e
-- title:
--   Br A: s Sup le pow
-- statement:
--   The Br A construction uses the s Sup le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L19-L27

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BrA.sSup_le_pow (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    sSup {e : ℕ | I ≤ v.asIdeal ^ e} = multiplicity v.asIdeal I := by sorry
