-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_iwU_coprime
-- name    : Formalism.L2.G.Triv.iwU_coprime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:38.164661+00:00
-- url     : https://prove2.me/theorems/a352d1fa-d9a9-4e94-a955-df88ed19d695
-- title:
--   Triv: iw U coprime
-- statement:
--   The Triv construction uses the iw U coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L177-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/OneAddPowOfSq.lean#L177-L217

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ClosureUpperUni
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OneAddPowOfMulSelfEqZero
import Definitions.Def_Lemmata_GeneralBFactLeftTail_Imports
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_OneAddPowOfSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {F : Type} [Field F] [NumberField F] {k : ℕ}

theorem Formalism.L2.G.Triv.iwU_coprime (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hg : g.Prime) (hgv : (g : 𝓞 F) ∈ v.asIdeal)
    (δ : GL (Fin k) (v.adicCompletion F)) (hδ : δ ∈ iwU F k v) (N : ℕ) (hc : Nat.Coprime N g) (hN : δ ^ N = 1) : δ = 1 := by sorry
