-- Prove2me | Theorems.Thm_ArtinKP_RC_smooth_chi
-- name    : ArtinKP.RC.smooth_chi
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:44:33.877973+00:00
-- url     : https://prove2.me/theorems/42df882c-6787-4b66-8532-d57f290171f6
-- title:
--   ArtinKP.RC.smooth_chi: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.RC`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Module Filter`, `open ArtinKP.X ArtinKP.B1`):
--
--   ```lean
--   theorem smooth_chi (S : Finset (FinitePlace F)) (n : ℕ) : X.Smooth fun P : X F => (chi S n P : ℂ)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.Smooth` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.RC.chi` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proof of `ArtinKP.RC.exists_isWeakSol_of_lap_eq` of this split imports it.
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

theorem smooth_chi (S : Finset (FinitePlace F)) (n : ℕ) : X.Smooth fun P : X F => (chi S n P : ℂ) := by
  sorry

end

end ArtinKP.RC
end
