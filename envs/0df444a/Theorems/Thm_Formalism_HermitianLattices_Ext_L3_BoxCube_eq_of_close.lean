-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxCube_eq_of_close
-- name    : Formalism.HermitianLattices.Ext.L3.BoxCube.eq_of_close
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:56.900811+00:00
-- url     : https://prove2.me/theorems/c8ce1b54-bd34-4a79-9574-6b230a9fd3fb
-- title:
--   Box Cube: eq of close
-- statement:
--   The Box Cube construction uses the eq of close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormLeOfMemIdeal.lean#L29-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormLeOfMemIdeal.lean#L29-L52

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxCube
open BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxCube.eq_of_close (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {b : Ideal (𝓞 F)} {δ : ℝ}
    (hδ : δ ^ Formalism.HermitianLatticesTheory.fDeg K ≤ (Ideal.absNorm b : ℝ)) {n n' : 𝓞 F} (hn : n ∈ b) (hn' : n' ∈ b)
    (hc : ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n - rEmb w n'| < δ) : n = n' := by sorry
