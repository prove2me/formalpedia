-- Prove2me | Theorems.Thm_ArtinKP_X_X_exists_isWeakSol_of_lap_eq_of_cutoff
-- name    : ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:58.766323+00:00
-- url     : https://prove2.me/theorems/e9fabb7c-3726-456f-aa3e-1a128801ad19
-- title:
--   ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   theorem X.exists_isWeakSol_of_lap_eq_of_cutoff {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u)
--       (hf2 : X.L2Rep Γ f) (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P)
--       (χ : ℕ → X F → ℝ) (hχs : ∀ n, X.Smooth fun P => (χ n P : ℂ))
--       (hχinv : ∀ n, X.IsInv Γ (χ n))
--       (hχK : ∀ n, ∃ K : Set (X F), IsCompact K ∧ ∀ P, χ n P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
--       (hχ0 : ∀ n P, 0 ≤ χ n P) (hχ1 : ∀ n P, χ n P ≤ 1)
--       (hχlim : ∀ P, Tendsto (fun n => χ n P) atTop (𝓝 1))
--       (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
--       (hgrad : ∀ n P, X.grad2 (fun P => (χ n P : ℂ)) P ≤ ε n) :
--       ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
--         (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X`, `ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.H3.instMeasurableSpace`, `ArtinKP.X.X.Smooth` and `ArtinKP.X.X.lap` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.IsInv`, `ArtinKP.X.X.L2Rep` and `ArtinKP.X.X.quotVol` (definitions bundle `ArtinKPB010` of this split); `ArtinKP.X.X.L2` and `ArtinKP.X.X.toL2` (definitions bundle `ArtinKPB011` of this split); `ArtinKP.X.X.grad2` (definitions bundle `ArtinKPB014` of this split); `ArtinKP.CAbs.EnergySpace.IsWeakSol`, `ArtinKP.CAbs.EnergySpace`, `ArtinKP.X.SymmOp.Core`, `ArtinKP.X.SymmOp.instInnerProductSpaceComplexCore`, `ArtinKP.X.SymmOp.instSeminormedAddCommGroupCore`, `ArtinKP.X.X.H1`, `ArtinKP.X.X.energy` and `ArtinKP.X.X.symmOp` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.RC.exists_isWeakSol_of_lap_eq` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

theorem X.exists_isWeakSol_of_lap_eq_of_cutoff {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u)
    (hf2 : X.L2Rep Γ f) (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P)
    (χ : ℕ → X F → ℝ) (hχs : ∀ n, X.Smooth fun P => (χ n P : ℂ))
    (hχinv : ∀ n, X.IsInv Γ (χ n))
    (hχK : ∀ n, ∃ K : Set (X F), IsCompact K ∧ ∀ P, χ n P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
    (hχ0 : ∀ n P, 0 ≤ χ n P) (hχ1 : ∀ n P, χ n P ≤ 1)
    (hχlim : ∀ P, Tendsto (fun n => χ n P) atTop (𝓝 1))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hgrad : ∀ n P, X.grad2 (fun P => (χ n P : ℂ)) P ≤ ε n) :
    ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
      (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x := by
  sorry

end

end ArtinKP.X
end
