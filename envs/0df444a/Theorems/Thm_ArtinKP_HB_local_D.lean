-- Prove2me | Theorems.Thm_ArtinKP_HB_local_D
-- name    : ArtinKP.HB.local_D
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:59.043319+00:00
-- url     : https://prove2.me/theorems/cb4e970f-20e0-4922-846c-6b651a8c8990
-- title:
--   ArtinKP.HB.local_D: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.HB`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S`, `open WithZero`, `open scoped Classical`):
--
--   ```lean
--   theorem local_D (m : PIdx 𝔟 → SInt 𝔪)
--       (hm : ∀ Q : PIdx 𝔟, v Q ≠ 0 →
--         m Q * ccof g 𝔟 v Q - 1 ∈ Q.1.map (algebraMap (𝓞 F) (SInt 𝔪)))
--       {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
--       L3V.Wsph g P ((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ)
--           ((rowElt g (H0.rowOf h𝔪 g μ) : F) *
--             (g.gen P : F) ^ (-((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ))) *
--         (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
--           (if v ⟨P, hPb⟩ = 0 then 1
--             else sAddChar 𝔪 ((((μ : SInt 𝔪) * γ.1 0 0 * m ⟨P, hPb⟩ : SInt 𝔪) : F) /
--               (g.gen P : F)))
--           else 1) *
--         (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
--           (if v ⟨P, hPb⟩ = 0 then 1 else sexticResidueSymbol ι 𝔪 P (γ.1 1 1) ^ 2)
--           else 1)⁻¹ *
--         ((L3V.uSym g P ((μ : SInt 𝔪) : F) ^ 2) ^ (L3V.vP P (cdig g 𝔟 v : F)) *
--           ((L3V.uSym g P (cdig g 𝔟 v : F) ^ 2) ^ (L3V.vP P ((μ : SInt 𝔪) : F)))⁻¹)⁻¹ =
--       H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P)
--   ```
--
--   **Definitions.** The statement is written with `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinKP.H.Dig`, `ArtinKP.H.digLoc`, `ArtinKP.H.xdig`, `ArtinKP.H0.rowOf`, `ArtinKP.HB.PIdx`, `ArtinKP.HB.ccof`, `ArtinKP.HB.cdig`, `ArtinKP.HB.eNu`, `ArtinKP.HB.tNu`, `ArtinPrimitiveRoots.L3V.Wsph`, `ArtinPrimitiveRoots.L3V.uSym` and `ArtinPrimitiveRoots.L3V.vP` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.HB.digCoefNu_eq` of this split imports it.
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

namespace ArtinKP.HB

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S
open WithZero

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

section D

variable (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (hgood : ∀ (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hext : IsExterior 𝔪 P),
    C3I.Good 𝔪 (⟨P, hP, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) (v : H.Dig 𝔪 𝔟)
  (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
  (hc : γ.1 1 0 = cdig g 𝔟 v)
  (hd : ((γ.1 1 1 : SInt 𝔪) : F) = -((cdig g 𝔟 v : F) * H.xdig g 𝔟 v))
  (μ ν : {x : SInt 𝔪 // x ≠ 0})
  (hν : ((ν : SInt 𝔪) : F) = ((μ : SInt 𝔪) : F) * ((g.gen 𝔟 : F) / (cdig g 𝔟 v : F)) ^ 2)

include hz6 hgood h𝔟 hc hd hν

theorem local_D (m : PIdx 𝔟 → SInt 𝔪)
    (hm : ∀ Q : PIdx 𝔟, v Q ≠ 0 →
      m Q * ccof g 𝔟 v Q - 1 ∈ Q.1.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {P : Ideal (𝓞 F)} (hP : P.IsPrime) (hPe : IsExterior 𝔪 P) :
    L3V.Wsph g P ((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ)
        ((rowElt g (H0.rowOf h𝔪 g μ) : F) *
          (g.gen P : F) ^ (-((normalizedFactors (H0.rowOf h𝔪 g μ).1.1).count P : ℤ))) *
      (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
        (if v ⟨P, hPb⟩ = 0 then 1
          else sAddChar 𝔪 ((((μ : SInt 𝔪) * γ.1 0 0 * m ⟨P, hPb⟩ : SInt 𝔪) : F) /
            (g.gen P : F)))
        else 1) *
      (if hPb : P ∈ (normalizedFactors 𝔟).toFinset then
        (if v ⟨P, hPb⟩ = 0 then 1 else sexticResidueSymbol ι 𝔪 P (γ.1 1 1) ^ 2)
        else 1)⁻¹ *
      ((L3V.uSym g P ((μ : SInt 𝔪) : F) ^ 2) ^ (L3V.vP P (cdig g 𝔟 v : F)) *
        ((L3V.uSym g P (cdig g 𝔟 v : F) ^ 2) ^ (L3V.vP P ((μ : SInt 𝔪) : F)))⁻¹)⁻¹ =
    H.digLoc g 𝔟 v P (eNu h𝔪 g 𝔟 ν P) (tNu h𝔪 g 𝔟 ν P) := by
  sorry

end D

end

end ArtinKP.HB
end
