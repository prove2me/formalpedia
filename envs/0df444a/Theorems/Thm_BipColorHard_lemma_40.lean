-- Prove2me | Theorems.Thm_BipColorHard_lemma_40
-- name    : BipColorHard.lemma_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:32.233042+00:00
-- url     : https://prove2.me/theorems/ddd65228-3b34-4cb1-b578-6bdbfa836982
-- title:
--   Lemma 40 — $q=3$, $D=5$: no three-valued local maximum
-- statement:
--   Let $q=3$ and $d=4$. No positive stationary pair of $\Phi$ with three distinct coordinate values is a local maximum of $\Phi$.
--
--   This is the three-type exclusion for $q=3$, the case not covered by Lemma 33.
--
--   **Formalization Note** The manuscript's proof is an exact computer-assisted calculation. The statement here carries none of it.
--
--   Differences from the source:
--   - encoding: three distinct coordinate values → three types (`typeCount = 3`); reason: at a stationary pair $P_i=P_j$ exactly when $R_i=R_j$, p.33
--   - encoding: local maximum of $\Phi$ → local maximum in neighbourhoods of $\mathbb R^q\times\mathbb R^q$; reason: $\Phi$ is unchanged by positive scaling of either vector, so this agrees with local maximality under the normalizations
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 40, p.54 (PDF p.56)

import Definitions.Def_BipColorHard_Objective

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 40**, p.54 (PDF p.56), manuscript sha256 78a66d1f…. For `q = 3` and `d = 4`, no positive stationary pair with
three distinct coordinate values is a local maximum of `Φ`.

**Formalization Note.** At a stationary pair `P_i = P_j ⇔ R_i = R_j` (p.33, PDF p.35), so "three distinct coordinate
values" is "three types". The manuscript's proof is an exact computer-assisted calculation; none of it is in the
statement. -/
theorem lemma_40 (P R : Fin 3 → ℝ) (hst : IsStationary 4 P R) (h3 : typeCount P R = 3) :
    ¬ IsLocalMaxPhi 4 P R := by sorry

end BipColorHard
