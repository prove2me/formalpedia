-- Prove2me | Theorems.Thm_ArtinKP_N2_mD_eq_of_le
-- name    : ArtinKP.N2.mD_eq_of_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:11:40.111773+00:00
-- url     : https://prove2.me/theorems/645268a4-44c4-423e-b833-6e50136560f4
-- title:
--   ArtinKP.N2.mD_eq_of_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.N2`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots`, `open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N`):
--
--   ```lean
--   theorem mD_eq_of_le (h𝔪 : 𝔪 ≠ ⊥) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
--       {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hle : Γ' ≤ Γ) {s : ℂ} (hs : 2 < s.re)
--       {D D' : Set (InfinitePlace F → ℂ)} {n n' : ℕ} (hD : MeasurableSet D)
--       (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
--       (hcell : Cell Γ D n) (hD' : Cell Γ' D' n') : mD D' Ψ s = mD D Ψ s
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.S.TSection` (definitions bundle `ArtinKPB002` of this split); `ArtinKP.C5.Inv`, `ArtinKP.X.GammaN` and `ArtinKP.X.GammaN.shift` (definitions bundle `ArtinKPB015` of this split); `ArtinKP.N.Cell` and `ArtinKP.N.mD` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.N2.zRes_congr` of this split imports it.
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

attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

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

theorem mD_eq_of_le (h𝔪 : 𝔪 ≠ ⊥) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hle : Γ' ≤ Γ) {s : ℂ} (hs : 2 < s.re)
    {D D' : Set (InfinitePlace F → ℂ)} {n n' : ℕ} (hD : MeasurableSet D)
    (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
    (hcell : Cell Γ D n) (hD' : Cell Γ' D' n') : mD D' Ψ s = mD D Ψ s := by
  sorry

end

end ArtinKP.N2
end
