-- Prove2me | Theorems.Thm_ArtinKP_FA_prop54
-- name    : ArtinKP.FA.prop54
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:05:08.069968+00:00
-- url     : https://prove2.me/theorems/f64a3538-27e5-40fd-a86f-10659af1ae22
-- title:
--   ArtinKP.FA.prop54: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.FA`, with `open NumberField IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E`):
--
--   ```lean
--   theorem prop54 (hv : ¬ 𝔪 ≤ v.asIdeal)
--       (hsum : ∀ t ∈ T, Summable fun x : RowQ 𝔪 => gU (π := π) P hG hz6 Φ f s t x.out)
--       (hsum' : Summable fun y : RowQ 𝔪 =>
--         (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out * f (y.out.c : F) (y.out.d : F)) :
--       ∑ t ∈ T, ∑' x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
--         = (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
--               * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
--             * ∑' y : RowQ 𝔪, (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
--                 * f (y.out.c : F) (y.out.d : F)
--           + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
--               * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
--             * ∑' y : RowQ 𝔪,
--                 TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s y.out
--                   * f (y.out.c : F) (y.out.d : F)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.GSection`, `ArtinKP.S.Row`, `ArtinKP.S.absS`, `ArtinKP.S.GSection.twist`, `ArtinKP.S.Row.c`, `ArtinKP.S.Row.d` and `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.FA.PrimeElt` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.S.Row.instMulActionUnitsSInt` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.FA.IsReps`, `ArtinKP.FA.RowQ`, `ArtinKP.FA.gU`, `ArtinKP.FA.PrimeElt.coe_ne_zero`, `ArtinKP.S.GSection.sharp` and `ArtinKP.S.TSection.restrict` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.FB.U_eis_primeElt` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatX _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.FA

open ArtinKP.A ArtinKP.S ArtinKP.B7 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ} (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {v : HeightOneSpectrum (𝓞 F)} {π : SInt 𝔪} (H : PrimeElt ι 𝔪 v π) (Φ : GSection ι P 𝔪)

section main

variable {T : Finset (SInt 𝔪)} (hT : IsReps (π ^ 3) T)
  (hdeep : ∀ t ∈ T, ∀ (s : ℂ) (c d : F), Φ s c (d + c * ((t : F) / (π : F) ^ 3)) = Φ s c d)
  (f : F → F → ℂ) (s cc : ℂ)
  (hfπ : ∀ c d : F, f ((π : F) * c) ((π : F) * d) = cc * f c d)
  (hfU : ∀ (ε : (SInt 𝔪)ˣ) (c d : F), f (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
    = ((absS 𝔪 ((ε : SInt 𝔪) : F) : ℝ) : ℂ) ^ s * f c d)

include P H hT hdeep hfπ hfU in
theorem prop54 (hv : ¬ 𝔪 ≤ v.asIdeal)
    (hsum : ∀ t ∈ T, Summable fun x : RowQ 𝔪 => gU (π := π) P hG hz6 Φ f s t x.out)
    (hsum' : Summable fun y : RowQ 𝔪 =>
      (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out * f (y.out.c : F) (y.out.d : F)) :
    ∑ t ∈ T, ∑' x : RowQ 𝔪, gU (π := π) P hG hz6 Φ f s t x.out
      = (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 3
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s)))
          * ∑' y : RowQ 𝔪, (Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6 s y.out
              * f (y.out.c : F) (y.out.d : F)
        + (1 - (Nat.card (SInt 𝔪 ⧸ Ideal.span {π}) : ℂ) ^ 2
            * (cc ^ 3 * ((absS 𝔪 (π : F) : ℝ) : ℂ) ^ (-(3 * s))))
          * ∑' y : RowQ 𝔪,
              TSection.restrict v hv ((Φ.sharp hG (π : F) H.coe_ne_zero).twist hG hz6) s y.out
                * f (y.out.c : F) (y.out.d : F) := by
  sorry

end main

end ArtinKP.FA
end
end
