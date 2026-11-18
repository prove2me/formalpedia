-- Prove2me | Theorems.Thm_ArtinKP_HB_loc_weyl
-- name    : ArtinKP.HB.loc_weyl
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:09:56.194264+00:00
-- url     : https://prove2.me/theorems/43483d82-b484-4662-8e02-434df9e2d304
-- title:
--   ArtinKP.HB.loc_weyl: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.HB`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots ArtinKP.A ArtinKP.S`, `open WithZero`, `open scoped Classical`):
--
--   ```lean
--   theorem loc_weyl {e : ℕ} {t : F} (ht : w.valuation F t = 1)
--       {y : SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0)
--       (μ a d m cc : SInt 𝔪) (U : ℂ) (hU : U ^ 6 = 1)
--       (hls : L3V.localSymbol ι 𝔪 w.asIdeal t =
--         U * (sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2)⁻¹)
--       (hd : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d =
--         -(Ideal.Quotient.mk _ cc * y))
--       (had : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) a *
--         Ideal.Quotient.mk _ d = 1)
--       (hm : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) m *
--         Ideal.Quotient.mk _ cc = 1)
--       (hμ0 : e = 0 → L3V.res 𝔪 w t * Ideal.Quotient.mk _ cc ^ 2 = Ideal.Quotient.mk _ μ)
--       (hμ1 : e ≠ 0 → Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) μ = 0) :
--       U ^ (2 * e) * L3V.Wv g w.asIdeal e *
--           sAddChar 𝔪 (((μ * a * m : SInt 𝔪) : F) / (g.gen w.asIdeal : F)) *
--           (sexticResidueSymbol ι 𝔪 w.asIdeal d ^ 2)⁻¹ *
--           ((U ^ 2) ^ (1 : ℤ) * ((sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2) ^ (e : ℤ))⁻¹)⁻¹ =
--         L3V.Wweyl g w.asIdeal ((e : ℤ) - 2) t y
--   ```
--
--   **Definitions.** The statement is written with `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinPrimitiveRoots.L3V.Wv`, `ArtinPrimitiveRoots.L3V.Wweyl`, `ArtinPrimitiveRoots.L3V.localSymbol` and `ArtinPrimitiveRoots.L3V.res` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.HB.local_D` of this split imports it.
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

section loc

variable {w : HeightOneSpectrum (𝓞 F)} (h : C3I.Good 𝔪 w) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
  (g : AllowedGen ι 𝔪)

include h

variable [Fintype (SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))]

include hω

theorem loc_weyl {e : ℕ} {t : F} (ht : w.valuation F t = 1)
    {y : SInt 𝔪 ⧸ w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0)
    (μ a d m cc : SInt 𝔪) (U : ℂ) (hU : U ^ 6 = 1)
    (hls : L3V.localSymbol ι 𝔪 w.asIdeal t =
      U * (sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2)⁻¹)
    (hd : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) d =
      -(Ideal.Quotient.mk _ cc * y))
    (had : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) a *
      Ideal.Quotient.mk _ d = 1)
    (hm : Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) m *
      Ideal.Quotient.mk _ cc = 1)
    (hμ0 : e = 0 → L3V.res 𝔪 w t * Ideal.Quotient.mk _ cc ^ 2 = Ideal.Quotient.mk _ μ)
    (hμ1 : e ≠ 0 → Ideal.Quotient.mk (w.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) μ = 0) :
    U ^ (2 * e) * L3V.Wv g w.asIdeal e *
        sAddChar 𝔪 (((μ * a * m : SInt 𝔪) : F) / (g.gen w.asIdeal : F)) *
        (sexticResidueSymbol ι 𝔪 w.asIdeal d ^ 2)⁻¹ *
        ((U ^ 2) ^ (1 : ℤ) * ((sexticResidueSymbol ι 𝔪 w.asIdeal cc ^ 2) ^ (e : ℤ))⁻¹)⁻¹ =
      L3V.Wweyl g w.asIdeal ((e : ℤ) - 2) t y := by
  sorry

end loc

end

end ArtinKP.HB
end
