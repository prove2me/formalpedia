-- Prove2me | Theorems.Thm_ArtinKP_B_fourier_coeff
-- name    : ArtinKP.B.fourier_coeff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:57.82707+00:00
-- url     : https://prove2.me/theorems/d988a297-d924-4356-a265-8417856e637e
-- title:
--   ArtinKP.B.fourier_coeff: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.B`, with `open scoped MatrixGroups ComplexConjugate Pointwise`, `open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K`):
--
--   ```lean
--   theorem fourier_coeff (ν : SInt 𝔪) (hV : ValidDepth hG Φ (ν : F) M) (hs : 2 < s.re)
--       {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
--       (hDfin : volume D ≠ ⊤) :
--       ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
--         = Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s * (∫ x in D, chiInf (ν : F) x)
--           + ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
--             * ∑' a : Cls (SInt 𝔪),
--                 B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
--                   * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.CubicPkg` and `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.B.psiS`, `ArtinKP.B.transLat`, `ArtinKP.B7.gauss`, `ArtinKP.B7.sAdd`, `ArtinKP.E.Cls`, `ArtinKP.E.nrm`, `ArtinKP.E.rp`, `ArtinKP.S.GSection`, `ArtinKP.S.lam`, `ArtinKP.S.vol`, `ArtinKP.S2.cubicSymbol` and `ArtinKP.S.GSection.twist` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.X.X.mk` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B.ValidDepth`, `ArtinKP.B.Winf`, `ArtinKP.B.chiInf` and `ArtinKP.B.eis` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds`, `ArtinKP.F.const_adm`, `ArtinKP.F.mD_restrict`, `ArtinKP.T.coeffFunctional_theta_twist_eq` and `ArtinKP.T.hasCoef_transLat` of this split import it.
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
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB015

section

attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (s : ℂ) (v : InfinitePlace F → ℝ) (hv : ∀ w, 0 < v w) (M : ℤ)

include hz6 in
theorem fourier_coeff (ν : SInt 𝔪) (hV : ValidDepth hG Φ (ν : F) M) (hs : 2 < s.re)
    {D : Set (InfinitePlace F → ℂ)} (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume)
    (hDfin : volume D ≠ ⊤) :
    ∫ x in D, eis (Φ.twist hG hz6) s (X.mk x v hv) * chiInf (ν : F) x
      = Φ s 0 1 * ((∏ w, v w : ℝ) : ℂ) ^ s * (∫ x in D, chiInf (ν : F) x)
        + ((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Winf s (ν : F) v
          * ∑' a : Cls (SInt 𝔪),
              B7.gauss (S2.cubicSymbol ι P hG hz6) (B7.sAdd 𝔪 hG.ne_bot) ν (rp a.1)
                * lam (psiS hG.ne_bot) M Φ ((rp a.1 : SInt 𝔪) : F) (ν : F) s * nrm (rp a.1) ^ (-s) := by
  sorry

end ArtinKP.B
end
end
