-- Prove2me | Theorems.Thm_ArtinKP_N2_zRes_congr
-- name    : ArtinKP.N2.zRes_congr
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:11:50.499214+00:00
-- url     : https://prove2.me/theorems/e5ce334b-502d-44bb-a667-9c72ee991b75
-- title:
--   ArtinKP.N2.zRes_congr: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N2`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem zRes_congr (hG : Good 𝔪) {Γ₁ Γ₂ : Subgroup (SL(2, 𝓞 F))} [Γ₁.FiniteIndex]
--       [Γ₂.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ₁ : Inv Γ₁ Ψ) (hΓ₂ : Inv Γ₂ Ψ)
--       {D₁ D₂ : Set (InfinitePlace F → ℂ)} {n₁ n₂ : ℕ} (hD₁ : Cell Γ₁ D₁ n₁) (hn₁ : 1 ≤ n₁)
--       (hD₂ : Cell Γ₂ D₂ n₂) (hn₂ : 1 ≤ n₂) : zRes Γ₁ Ψ D₁ n₁ = zRes Γ₂ Ψ D₂ n₂
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.A.Good` (definitions bundle `ArtinKPB000` of this split); `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.C5.Inv` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.Cell` and `ArtinKP.N.zRes` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.N2.cusp_integral_eq_zero` and `ArtinKP.N2.zRes_eq_zPsi` of this split import it.
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

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N2

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

theorem zRes_congr (hG : Good 𝔪) {Γ₁ Γ₂ : Subgroup (SL(2, 𝓞 F))} [Γ₁.FiniteIndex]
    [Γ₂.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ₁ : Inv Γ₁ Ψ) (hΓ₂ : Inv Γ₂ Ψ)
    {D₁ D₂ : Set (InfinitePlace F → ℂ)} {n₁ n₂ : ℕ} (hD₁ : Cell Γ₁ D₁ n₁) (hn₁ : 1 ≤ n₁)
    (hD₂ : Cell Γ₂ D₂ n₂) (hn₂ : 1 ≤ n₂) : zRes Γ₁ Ψ D₁ n₁ = zRes Γ₂ Ψ D₂ n₂ := by
  sorry

end

end ArtinKP.N2
end
