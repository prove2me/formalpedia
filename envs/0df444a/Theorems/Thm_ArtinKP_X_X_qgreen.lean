-- Prove2me | Theorems.Thm_ArtinKP_X_X_qgreen
-- name    : ArtinKP.X.X.qgreen
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:37.356358+00:00
-- url     : https://prove2.me/theorems/0b48f670-09f1-4e79-acca-61047e4d01b8
-- title:
--   ArtinKP.X.X.qgreen: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.qgreen {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ u : X F → ℂ} (hφ : X.Smooth φ)
--       (hc : HasCompactSupport φ) (hu : X.Smooth u) (hinv : X.IsInv Γ u) :
--       ∫ P, (((η P).toReal : ℝ) : ℂ) * (X.avg Γ φ P * X.lap u P) ∂X.vol F =
--         ∫ P, (((η P).toReal : ℝ) : ℂ) * X.gam (X.avg Γ φ) u P ∂X.vol F
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.Smooth`, `ArtinKP.X.X.avg`, `ArtinKP.X.X.lap` and `ArtinKP.X.X.vol` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.IsPOU` (definitions bundle `ArtinKPB008` of this split); `ArtinKP.X.X.IsInv` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.gam` (definitions bundle `ArtinKPB013` of this split).
--
--   **Used by.** The proofs of `ArtinKP.X.X.ims` and `ArtinKP.X.X.inner_coreLap_eq` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB010
import Definitions.Def_ArtinKPB013

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

variable {Γ : Subgroup (SL(2, 𝓞 F))}

theorem X.qgreen {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ u : X F → ℂ} (hφ : X.Smooth φ)
    (hc : HasCompactSupport φ) (hu : X.Smooth u) (hinv : X.IsInv Γ u) :
    ∫ P, (((η P).toReal : ℝ) : ℂ) * (X.avg Γ φ P * X.lap u P) ∂X.vol F =
      ∫ P, (((η P).toReal : ℝ) : ℂ) * X.gam (X.avg Γ φ) u P ∂X.vol F := by
  sorry

end

end ArtinKP.X
end
