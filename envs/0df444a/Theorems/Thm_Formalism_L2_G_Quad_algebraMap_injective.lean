-- Prove2me | Theorems.Thm_Formalism_L2_G_Quad_algebraMap_injective
-- name    : Formalism.L2.G.Quad.algebraMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:53.718672+00:00
-- url     : https://prove2.me/theorems/23d1e11b-202b-4f57-a3de-8bcfbd708ecb
-- title:
--   Quad: algebra Map injective
-- statement:
--   The Quad construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/AlgebraMapFinite.lean#L56-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/PerfectRings/AlgebraMapFinite.lean#L56-L58

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

theorem Formalism.L2.G.Quad.algebraMap_injective : Function.Injective (algebraMap R (QuadraticAlgebra R π 0)) := by sorry
