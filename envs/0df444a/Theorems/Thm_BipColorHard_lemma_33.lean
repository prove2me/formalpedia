-- Prove2me | Theorems.Thm_BipColorHard_lemma_33
-- name    : BipColorHard.lemma_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:13.577226+00:00
-- url     : https://prove2.me/theorems/c27ba815-4c64-4334-86dc-13ae54c97030
-- title:
--   Lemma 33 — no three-type local maximum
-- statement:
--   Let $q=2k+1\ge5$, $d=q$. No stationary pair of $\Phi$ with three types is a local maximum of $\Phi$.
--
--   Together with Lemma 29 this reduces the maximizers of $\Phi$ for $q\ge 5$ to two-type pairs.
--
--   Differences from the source:
--   - encoding: local maximum of $\Phi$ → local maximum in neighbourhoods of $\mathbb R^q\times\mathbb R^q$; reason: $\Phi$ is unchanged by positive scaling of either vector, so this agrees with local maximality under the normalizations
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 33, p.41 (PDF p.43); range of §7, p.30 (PDF p.32)

import Definitions.Def_BipColorHard_Objective

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 33**, p.41 (PDF p.43), manuscript sha256 78a66d1f…. Range of §7: `q = 2k + 1 ≥ 5`, `d = q`. No stationary
pair of `Φ` with three types is a local maximum. -/
theorem lemma_33 (k : ℕ) (hk : 2 ≤ k) (P R : Fin (2 * k + 1) → ℝ)
    (hst : IsStationary (2 * k + 1) P R) (h3 : typeCount P R = 3) :
    ¬ IsLocalMaxPhi (2 * k + 1) P R := by sorry

end BipColorHard
