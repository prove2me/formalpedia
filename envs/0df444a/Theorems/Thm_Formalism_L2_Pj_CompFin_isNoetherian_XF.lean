-- Prove2me | Theorems.Thm_Formalism_L2_Pj_CompFin_isNoetherian_XF
-- name    : Formalism.L2.Pj.CompFin.isNoetherian_XF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:25.016668+00:00
-- url     : https://prove2.me/theorems/aed3ee8b-9464-4b38-b05c-2933ec373bd6
-- title:
--   Comp Fin: is Noetherian XF
-- statement:
--   The Comp Fin construction uses the is Noetherian XF property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L38-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompFin.lean#L38-L59

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompFin
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.Pj.CompFin.isNoetherian_XF (Xo : Moduli Dw l) (c : Coeff l) : IsNoetherian (Xo.XF c) := by sorry
