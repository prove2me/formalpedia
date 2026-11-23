-- Prove2me | Theorems.Thm_Formalism_L2_Pj_betaAt_symm
-- name    : Formalism.L2.Pj.betaAt_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:53.690304+00:00
-- url     : https://prove2.me/theorems/6a70f480-8e3f-40f7-ad65-5aba09bbb525
-- title:
--   Pj: beta At symm
-- statement:
--   The Pj construction uses the beta At symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/BetaAtSymm.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/BetaAtSymm.lean#L40-L44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
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
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
variable {R : Type} [CommRing R] [IsDomain R]

theorem Formalism.L2.Pj.betaAt_symm (D : DegPre R) {C : Type} [NormedField C] (f : R →+* C) (p : ℕ) (a b : D.X) :
    betaAt D f p a b = betaAt D f p b a := by sorry
