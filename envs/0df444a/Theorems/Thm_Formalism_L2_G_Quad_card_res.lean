-- Prove2me | Theorems.Thm_Formalism_L2_G_Quad_card_res
-- name    : Formalism.L2.G.Quad.card_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:22.583982+00:00
-- url     : https://prove2.me/theorems/2f21e0a8-71ca-4430-b1ce-baacb539e081
-- title:
--   Quad: card res
-- statement:
--   The Quad construction uses the card res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/AlgebraMapFinite.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/AlgebraMapFinite.lean#L47-L50

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatRing
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Quad
open QuadraticAlgebra
variable {R : Type} [CommRing R] (π : R)

theorem Formalism.L2.G.Quad.card_res :
    Nat.card (QuadraticAlgebra R π 0 ⧸ Ideal.span {(ω : QuadraticAlgebra R π 0)}) =
      Nat.card (R ⧸ Ideal.span {π}) := by sorry
