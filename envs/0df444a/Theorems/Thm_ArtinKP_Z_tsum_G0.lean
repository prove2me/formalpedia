-- Prove2me | Theorems.Thm_ArtinKP_Z_tsum_G0
-- name    : ArtinKP.Z.tsum_G0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T10:11:38.183187+00:00
-- url     : https://prove2.me/theorems/ee8d4432-d21a-4bd5-aa0a-6de814d1a41a
-- title:
--   ArtinKP.Z.tsum_G0: intermediate lemma of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   An intermediate lemma of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The statement and its proof are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `ArtinKP.Z`, with `open NumberField ArtinPrimitiveRoots`):
--
--   ```lean
--   theorem tsum_G0 {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 4 / 3 < s.re) :
--       ∑' c, g0Term 𝔪 s c = C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2)
--   ```
--
--   **Definitions.** The statement is written with `ArtinKP.Z.g0Term` and `ArtinPrimitiveRoots.C3P.zetaS` (definitions bundle `ArtinKPB017` of this split).
--
--   **Used by.** The proof of `ArtinKP.BZ.exists_mean_eis_sumBig_eq_pole_four_thirds` of this split imports it.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017

section

attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin

set_option autoImplicit false

open NumberField ArtinPrimitiveRoots

namespace ArtinKP

namespace Z

variable {F : Type*} [Field F] [NumberField F]

theorem tsum_G0 {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {s : ℂ} (hs : 4 / 3 < s.re) :
    ∑' c, g0Term 𝔪 s c = C3P.zetaS 𝔪 (3 * s - 3) / C3P.zetaS 𝔪 (3 * s - 2) := by
  sorry

end Z

end ArtinKP
end
