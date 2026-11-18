-- Prove2me | Theorems.Thm_ArtinKP_C5_exists_single
-- name    : ArtinKP.C5.exists_single
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T09:42:29.600246+00:00
-- url     : https://prove2.me/theorems/c1744898-d400-4fd3-8394-702a33176d08
-- title:
--   ArtinKP.C5.exists_single: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.C5`, with `open scoped MatrixGroups ComplexConjugate ENNReal Topology`, `open MeasureTheory Set NumberField Filter`, `open ArtinKP.X ArtinKP.B1`):
--
--   ```lean
--   lemma exists_single (S : Finset (FinitePlace F)) (P₀ : X F) :
--       ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ p : PairClass S, p ≠ p₁ → p.ht P < 3 / 2
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.X.H3`, `ArtinKP.X.X` and `ArtinKP.X.H3.instTopologicalSpace` (definitions bundle `ArtinKPB005` of this split); `ArtinKP.B1.PairClass` and `ArtinKP.B1.PairClass.ht` (definitions bundle `ArtinKPB015` of this split).
--
--   **Used by.** The proofs of `ArtinKP.C5.exists_norm_hpart_le`, `ArtinKP.C5.lap_upart`, `ArtinKP.C5.norm_upart_le`, `ArtinKP.C5.smooth_src`, `ArtinKP.C5.tendsto_ray_functional_resPart_theta`, `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.F.zPsi_restrict_twist`, `ArtinKP.GK.theta_per_gen_of_isExterior`, `ArtinKP.N2.integrable_orbit`, `ArtinKP.N2.orbit_integral_eq_zero`, `ArtinKP.N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero`, `ArtinKP.N2.zRes_congr`, `ArtinKP.N.cf_theta`, `ArtinKP.N.cf_theta_translate`, `ArtinKP.N.coeff_resPart_add_hInt`, `ArtinKP.N.differentiableOn_Acoef`, `ArtinKP.N.differentiable_hInt`, `ArtinKP.N.integral_box_theta_eq_of_tendsto_ray`, `ArtinKP.N.tendsto_ray_Acoef`, `ArtinKP.T.differentiableOn_Afun` and `ArtinKP.T.tendsto_ray_Afun` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinKPB015

section

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.C5

open ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

lemma exists_single (S : Finset (FinitePlace F)) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ p : PairClass S, p ≠ p₁ → p.ht P < 3 / 2 := by
  sorry

end

end ArtinKP.C5
end
