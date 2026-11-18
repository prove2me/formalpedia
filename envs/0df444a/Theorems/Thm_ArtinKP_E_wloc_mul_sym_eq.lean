-- Prove2me | Theorems.Thm_ArtinKP_E_wloc_mul_sym_eq
-- name    : ArtinKP.E.wloc_mul_sym_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:03:39.136035+00:00
-- url     : https://prove2.me/theorems/ad38a8ac-2625-4dc8-94bc-c314afdad63a
-- title:
--   ArtinKP.E.wloc_mul_sym_eq: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.E`, with `open NumberField IsDedekindDomain UniqueFactorizationMonoid`, `open ArtinPrimitiveRoots ArtinKP.B7`):
--
--   ```lean
--   theorem wloc_mul_sym_eq (e : ℕ) {ν c : SInt 𝔪} (hν : ν = c * g.gen v.asIdeal ^ e) :
--       Theta.wloc (nrm (g.gen v.asIdeal)) (nrm (g.gen v.asIdeal) ^ (-(4 / 3 : ℂ)))
--           (L3V.tau g v.asIdeal 4) e * S.sym c (g.gen v.asIdeal) ^ e =
--         (((Ideal.absNorm v.asIdeal : ℝ) ^ ((e : ℝ) / 3) : ℝ) : ℂ) *
--           L3V.Wsph g v.asIdeal (e : ℤ) ((ν : F) * (g.gen v.asIdeal : F) ^ (-(e : ℤ)))
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.B7.CubicSymbol` and `ArtinKP.E.nrm` (definitions bundle `ArtinKPB002` of this split); `ArtinPrimitiveRoots.C3I.Good` (definitions bundle `ArtinKPB003` of this split); `ArtinPrimitiveRoots.L3V.Wsph`, `ArtinPrimitiveRoots.L3V.tau` and `ArtinKP.E.Theta.wloc` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proofs of `ArtinKP.GK.tau_eq_rpow_mul_coefF_mul_kir` and `ArtinKP.GR.thmE` of this split import it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinKP.E

open ArtinPrimitiveRoots ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section prime

variable {v : HeightOneSpectrum (𝓞 F)} {ι : F →+* ℂ}
variable (h : C3I.Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (g : AllowedGen ι 𝔪)
  (h𝔪 : 𝔪 ≠ ⊥) (S : CubicSymbol (SInt 𝔪))
  (hS : ∀ d : SInt 𝔪, S.sym d (g.gen v.asIdeal) = sexticResidueSymbol ι 𝔪 v.asIdeal d ^ 2)

include h hω hS h𝔪 in
theorem wloc_mul_sym_eq (e : ℕ) {ν c : SInt 𝔪} (hν : ν = c * g.gen v.asIdeal ^ e) :
    Theta.wloc (nrm (g.gen v.asIdeal)) (nrm (g.gen v.asIdeal) ^ (-(4 / 3 : ℂ)))
        (L3V.tau g v.asIdeal 4) e * S.sym c (g.gen v.asIdeal) ^ e =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ ((e : ℝ) / 3) : ℝ) : ℂ) *
        L3V.Wsph g v.asIdeal (e : ℤ) ((ν : F) * (g.gen v.asIdeal : F) ^ (-(e : ℤ))) := by
  sorry

end prime

end ArtinKP.E
end
