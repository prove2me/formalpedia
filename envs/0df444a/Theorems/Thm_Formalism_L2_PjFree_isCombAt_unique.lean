-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_isCombAt_unique
-- name    : Formalism.L2.PjFree.isCombAt_unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:02.760421+00:00
-- url     : https://prove2.me/theorems/eee66ae3-f113-4e29-bd0b-cbd9ef2e3636
-- title:
--   Pj Free: is Comb At unique
-- statement:
--   The Pj Free construction uses the is Comb At unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L132-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntAllProofFree.lean#L132-L138

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ExistsOfValILeOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllProofFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.PjFree
open Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem Formalism.L2.PjFree.isCombAt_unique {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by sorry
