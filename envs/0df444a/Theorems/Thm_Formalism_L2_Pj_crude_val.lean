-- Prove2me | Theorems.Thm_Formalism_L2_Pj_crude_val
-- name    : Formalism.L2.Pj.crude_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:43.574204+00:00
-- url     : https://prove2.me/theorems/86082aa5-1d59-4ae4-9567-20e9e8c8aa76
-- title:
--   Pj: crude val
-- statement:
--   The Pj construction uses the crude val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ConjNeSelfOfCM.lean#L93-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ConjNeSelfOfCM.lean#L93-L187

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]

theorem Formalism.L2.Pj.crude_val {T : CDVR} {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB T.Fr d O) (h : PS T.Fr 2 d)
    (hg : B.IsCanonGauge T.Fr h) (w0 : O) (k : ℕ) (uvec : Lt1 Dw → Fin d → T.Fr) (hsat : SatDir T uvec)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ha : DomW Dw a) (hn : Fintype.card (Lt1 Dw) ≤ n) :
    P1 Dw T a hn ∈ FFV (Dw := Dw) T a n ∧ ∃ f : PS T.Fr n d, IsIntPS T f ∧ Crude.OrdGe (DF Dw a) f ∧
      nabValN B T.Fr h w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ => uvec ⟨ℓ.1, ℓ.2.1⟩) (P1 Dw T a hn) =
        (fact1 Dw a hn : T.Fr) := by sorry
