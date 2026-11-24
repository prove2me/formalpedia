-- Prove2me | Theorems.Thm_Formalism_NG_genfin_ker_map_uncurry
-- name    : Formalism.NG.genfin_ker_map_uncurry
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:14.587924+00:00
-- url     : https://prove2.me/theorems/cb0289df-0e99-4f33-b3bc-b6b1972ad93d
-- title:
--   NG: genfin ker map uncurry
-- statement:
--   The NG construction uses the genfin ker map uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L155-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/GenFin.lean#L155-L168

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_StatementG
import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenRelMapApply
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
variable {R : Type*} [Ring R] {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {m g d : Type} [Fintype m] [Fintype g] [DecidableEq g] [Fintype d] [DecidableEq d]
  (ρ : R →+* Matrix d d O) [SMulCommClass R O (LatQ O d ρ)]

theorem Formalism.NG.genfin_ker_map_uncurry (P : Matrix m g R) :
    (LinearMap.ker (relMap O (LatQ O d ρ) P)).map (uncurryEquiv (g := g) ρ).toLinearMap =
      LinearMap.ker (relMap O (KO O) (fun (p : m × d) (q : g × d) => ρ (P p.1 q.1) p.2 q.2)) := by sorry
