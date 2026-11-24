-- Prove2me | Theorems.Thm_Formalism_L2_Pj_valV_wchar_eq_one
-- name    : Formalism.L2.Pj.valV_wchar_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.115959+00:00
-- url     : https://prove2.me/theorems/cd626230-5244-4804-b9eb-5f49a9be0ae4
-- title:
--   Pj: val V wchar eq one
-- statement:
--   The Pj construction uses the val V wchar eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CoreProofs.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CoreProofs.lean#L42-L44

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CoreProofs
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
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem Formalism.L2.Pj.valV_wchar_eq_one {T : CDVR} (e : Ix Dw → ℕ) (t : Ix Dw → T.Frˣ)
    (ht : ∀ i, valV T.V ((t i : T.Frˣ) : T.Fr) = 1) : valV T.V (wchar e t) = 1 := by sorry
