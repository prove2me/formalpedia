-- Prove2me | Theorems.Thm_Formalism_L2_Pj_htSup_of
-- name    : Formalism.L2.Pj.htSup_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:22.0172+00:00
-- url     : https://prove2.me/theorems/0ef8ec2f-9965-5f5e-bbec-2cc9719615ca
-- title:
--   Pj: ht Sup of
-- statement:
--   The Pj construction uses the ht Sup of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L102-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AxHSup.lean#L102-L147

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_PTNonempty
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]

theorem Formalism.L2.Pj.htSup_of (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)
    (hfn : FnNe Xo c fn) (hfg : FnFG Xo c) (hcx : ValAtCx h yP)
    (huta1 : wtZ uta1.1 uta1.2 = (2 : ℕ) • (wtZ uL.1 uL.2 - wtZ ude.1 ude.2))
    (huta2 : wtZ uta2.1 uta2.2 = (Dd + 4 : ℕ) • wtZ uL.1 uL.2 - wtZ uF.1 uF.2)
    (hwS : ∀ k, wR k ∈ sec Xo c uL.1 uL.2) (hwB : ∀ k, SupBdd Xo c fn uL.1 uL.2 (wR k)) (hwN : ∀ k, NZSome h (wR k))
    (hpS : ∀ k, thpR k ∈ sec Xo c uF.1 uF.2) (hpB : ∀ k, SupBdd Xo c fn uF.1 uF.2 (thpR k))
    (hpN : ∀ k, NZSome h (thpR k))
    (h1S : ta1R ∈ sec Xo c uta1.1 uta1.2) (h1B : SupBdd Xo c fn uta1.1 uta1.2 ta1R) (h1N : NZSome h ta1R)
    (h2S : ta2R ∈ sec Xo c uta2.1 uta2.2) (h2B : SupBdd Xo c fn uta2.1 uta2.2 ta2R) (h2N : NZSome h ta2R)
    (mx : (c.F →+* ℂ) → ℝ) (hmx : ∀ σ k, Real.log (supR Xo c fn σ uL.1 uL.2 (wR k)) ≤ mx σ)
    (hmxm : meanK mx ≤ Gc * wsize (wtZ uL.1 uL.2))
    (hth : ∀ k, meanK (fun σ => Real.log (supR Xo c fn σ uF.1 uF.2 (thpR k))) ≤ Gc * wsize (wtZ uF.1 uF.2))
    (hta1 : meanK (fun σ => Real.log (supR Xo c fn σ uta1.1 uta1.2 ta1R)) ≤ 2 * PI4 * Dd * wsize (wtZ uL.1 uL.2))
    (hta2 : meanK (fun σ => Real.log (supR Xo c fn σ uta2.1 uta2.2 ta2R)) ≤ PI4 * Dd * wsize (wtZ uL.1 uL.2)) :
    (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip
      wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).HtSup := by sorry
