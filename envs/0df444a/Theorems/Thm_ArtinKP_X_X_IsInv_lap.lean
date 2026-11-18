-- Prove2me | Theorems.Thm_ArtinKP_X_X_IsInv_lap
-- name    : ArtinKP.X.X.IsInv.lap
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:28:59.176014+00:00
-- url     : https://prove2.me/theorems/8e57b8fd-d04d-4a7c-8b14-993b8c7a147e
-- title:
--   ArtinKP.X.X.IsInv.lap: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.X`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter`, `open Classical`):
--
--   ```lean
--   lemma X.IsInv.lap {u : X F → ℂ} (hinv : X.IsInv Γ u) (hu : X.Smooth u) : X.IsInv Γ (X.lap u)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.X` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.X.X.Smooth` and `ArtinKP.X.X.lap` (definitions bundle `ArtinKPB006` of this split); `ArtinKP.X.X.IsInv` (definitions bundle `ArtinKPB010` of this split).
--
--   **Used by.** The proofs of `ArtinKP.X.X.ims` and `ArtinKP.X.X.qgreen` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB010

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

lemma X.IsInv.lap {u : X F → ℂ} (hinv : X.IsInv Γ u) (hu : X.Smooth u) : X.IsInv Γ (X.lap u) := by
  sorry

end

end ArtinKP.X
end
