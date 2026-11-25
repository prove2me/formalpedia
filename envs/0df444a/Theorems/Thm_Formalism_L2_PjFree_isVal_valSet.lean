-- Prove2me | Theorems.Thm_Formalism_L2_PjFree_isVal_valSet
-- name    : Formalism.L2.PjFree.isVal_valSet
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:46:49.104856+00:00
-- url     : https://prove2.me/theorems/be3fe5c2-3ade-4cbf-893f-8ad52e56d211
-- title:
--   Pj Free: is Val val Set
-- statement:
--   The Pj Free construction uses the is Val val Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PtFree.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PtFree.lean#L78-L80

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RulInst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
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
open Formalism.L2.Pj NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
  (cls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop)
variable {Xo c cls}

theorem Formalism.L2.PjFree.isVal_valSet (la : HeightOneSpectrum (𝓞 c.F)) : ∀ v ∈ valSet Xo c cls la, IsVal la v := by sorry
