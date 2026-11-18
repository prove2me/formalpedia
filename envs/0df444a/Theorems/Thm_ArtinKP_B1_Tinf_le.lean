-- Prove2me | Theorems.Thm_ArtinKP_B1_Tinf_le
-- name    : ArtinKP.B1.Tinf_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:19.59455+00:00
-- url     : https://prove2.me/theorems/9fa4fb57-6255-416a-8ac9-7cf0340f2ed4
-- title:
--   ArtinKP.B1.Tinf_le: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.B1`, with `open scoped MatrixGroups ComplexConjugate ENNReal`, `open MeasureTheory Set NumberField Module`, `open ArtinKP.X`):
--
--   ```lean
--   theorem Tinf_le (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) :
--       ∃ K : ℝ, 0 < K ∧ ∀ Q : X F, Tinf S σ Q ≤ K * (X.ht Q ^ (2 - σ) + X.ht Q ^ (-σ))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B1.Tinf` and `ArtinKP.X.X.ht` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.B1.lintegral_G_pow_lt_top`, `ArtinKP.N2.mD_eq_of_le` and `ArtinKP.N.cf_eis` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

theorem Tinf_le (S : Finset (FinitePlace F)) {σ : ℝ} (hσ : 2 < σ) :
    ∃ K : ℝ, 0 < K ∧ ∀ Q : X F, Tinf S σ Q ≤ K * (X.ht Q ^ (2 - σ) + X.ht Q ^ (-σ)) := by
  sorry

end

end ArtinKP.B1
end
