-- Prove2me | Theorems.Thm_ArtinKP_RC_exists_single
-- name    : ArtinKP.RC.exists_single
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:43:52.551582+00:00
-- url     : https://prove2.me/theorems/43e3299b-79e2-413d-b3ca-25569bc34411
-- title:
--   ArtinKP.RC.exists_single: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.RC`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Module Filter`, `open ArtinKP.X ArtinKP.B1`):
--
--   ```lean
--   lemma exists_single (S : Finset (FinitePlace F)) (n : ℕ) (P₀ : X F) :
--       ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ p : PairClass S, p ≠ p₁ →
--         theta (Real.log (p.ht P) / ((n : ℝ) + 1)) = 0
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B1.PairClass`, `ArtinKP.RC.theta` and `ArtinKP.B1.PairClass.ht` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.RC.exists_isWeakSol_of_lap_eq`, `ArtinKP.RC.grad2_chi_le` and `ArtinKP.RC.smooth_chi` of this split import it.
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

lemma exists_single (S : Finset (FinitePlace F)) (n : ℕ) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ p : PairClass S, p ≠ p₁ →
      theta (Real.log (p.ht P) / ((n : ℝ) + 1)) = 0 := by
  sorry

end

end ArtinKP.RC
end
