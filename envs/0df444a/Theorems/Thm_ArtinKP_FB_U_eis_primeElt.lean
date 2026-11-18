-- Prove2me | Theorems.Thm_ArtinKP_FB_U_eis_primeElt
-- name    : ArtinKP.FB.U_eis_primeElt
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:06:01.021585+00:00
-- url     : https://prove2.me/theorems/d2c67c38-a5eb-4412-9d4e-3d14d605088d
-- title:
--   ArtinKP.FB.U_eis_primeElt: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.FB`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B`):
--
--   ```lean
--   theorem U_eis_primeElt (hv : ¬ 𝔪 ≤ v.asIdeal) {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
--       (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
--       {s : ℂ} (hs : 2 < s.re) (Q : X F) :
--       U ((π : F) ^ 3) (pow_ne_zero 3 H.coe_ne_zero) T (eis (Φ.twist hG hz6) s) Q
--         = ((Nh ((π : F) ^ 3) : ℝ) : ℂ) ^ s *
--           ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
--               * ((((Ninf (π : F) : ℝ) : ℂ) ^ (-s)) ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
--               * eis ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s Q
--             + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
--               * ((((Ninf (π : F) : ℝ) : ℂ) ^ (-s)) ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
--               * eis (TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6))
--                   s Q)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection`, `ArtinKP.S.absS` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.FA.PrimeElt` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B.Ninf` and `ArtinKP.B.eis` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.FA.IsReps`, `ArtinKP.FB.Nh`, `ArtinKP.FB.U`, `ArtinKP.FA.PrimeElt.coe_ne_zero`, `ArtinKP.S.GSection.sharp` and `ArtinKP.S.TSection.restrict` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.F.mD_restrict` and `ArtinKP.GK.theta_per_gen_of_isExterior` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FB

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E ArtinKP.FA ArtinKP.X ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}

section main

variable (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {π : SInt 𝔪} (H : PrimeElt ι 𝔪 v π) (Φ : GSection ι P 𝔪)

variable [IsTotallyComplex F]

include H in
theorem U_eis_primeElt (hv : ¬ 𝔪 ≤ v.asIdeal) {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
    (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
    {s : ℂ} (hs : 2 < s.re) (Q : X F) :
    U ((π : F) ^ 3) (pow_ne_zero 3 H.coe_ne_zero) T (eis (Φ.twist hG hz6) s) Q
      = ((Nh ((π : F) ^ 3) : ℝ) : ℂ) ^ s *
        ((Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
            * ((((Ninf (π : F) : ℝ) : ℂ) ^ (-s)) ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
            * eis ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s Q
          + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
            * ((((Ninf (π : F) : ℝ) : ℂ) ^ (-s)) ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
            * eis (TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6))
                s Q) := by
  sorry

end main

end ArtinKP.FB
end
end
