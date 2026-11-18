-- Prove2me | Theorems.Thm_ArtinKP_RC_exists_isWeakSol_of_lap_eq
-- name    : ArtinKP.RC.exists_isWeakSol_of_lap_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:49.591899+00:00
-- url     : https://prove2.me/theorems/4e6dc395-ba1a-4230-874d-16ecd99b9d70
-- title:
--   ArtinKP.RC.exists_isWeakSol_of_lap_eq: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.RC`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Module Filter`, `open ArtinKP.X ArtinKP.B1`):
--
--   ```lean
--   theorem exists_isWeakSol_of_lap_eq (hB : SBezout S) (hO : FiniteCusps S) {Γ : Subgroup (SL(2, 𝓞 F))}
--       [Γ.FiniteIndex] {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u) (hf2 : X.L2Rep Γ f)
--       (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P) :
--       ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
--         (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.Smooth` and `ArtinKP.X.X.lap` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.L2Rep` and `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` and `ArtinKP.X.X.toL2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.B1.FiniteCusps`, `ArtinKP.B1.SBezout`, `ArtinKP.CAbs.EnergySpace.IsWeakSol`, `ArtinKP.CAbs.EnergySpace`, `ArtinKP.X.SymmOp.Core`, `ArtinKP.X.SymmOp.instInnerProductSpaceComplexCore`, `ArtinKP.X.SymmOp.instSeminormedAddCommGroupCore`, `ArtinKP.X.X.H1`, `ArtinKP.X.X.energy` and `ArtinKP.X.X.symmOp` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.N.coeff_resPart_add_hInt` and `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Module Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

theorem exists_isWeakSol_of_lap_eq (hB : SBezout S) (hO : FiniteCusps S) {Γ : Subgroup (SL(2, 𝓞 F))}
    [Γ.FiniteIndex] {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u) (hf2 : X.L2Rep Γ f)
    (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P) :
    ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
      (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x := by
  sorry

end

end ArtinKP.RC
end
