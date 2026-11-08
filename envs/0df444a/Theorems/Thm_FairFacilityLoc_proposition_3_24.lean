-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_24
-- name    : FairFacilityLoc.proposition_3_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:39.24099+00:00
-- url     : https://prove2.me/theorems/0b92134d-cc46-4692-9af3-f6aa34688201
-- title:
--   Proposition 3.24 — the share bound for large coordinates
-- statement:
--   For $d\in\{2,3\}$, if $\mathcal C>d$, every coordinate $r$ with $z_r>\tau_d$ satisfies the strict bound (3.23),
--   $$s_r<dz_r^2-(dz_r^2-1)\,\omega(v_r),\qquad v_r=\sqrt{\frac{1-z_r^2}{d-1}},$$
--   where $\omega$ is taken with $d$ and $b_d$.
--
--   This is the only part of the proof of $\mathcal C\le d$ that is checked separately in each dimension.
--
--   **Scope of the hypothesis** $\mathcal C>d$ is the contradiction assumption of the proof of Proposition 3.17, which shows that it never holds for normalized data satisfying the capacity condition. This statement is a step of that proof, as on the page.
--
--   Differences from the source:
--   - generalization: normalized coordinates of a mechanism output, where Lemma 3.9 holds → any normalized family with $Q_r(a)\le K_r$ for all $a,r$ (CapacityCondition); reason: the proof uses the mechanism only through this inequality; Lemma 3.9 (`lemma_3_9`) supplies it for a mechanism output
--   - encoding: the normalization (3.2), with the output at the origin → the structure IsNormalized; reason: the fields are the hypotheses (3.2) for a finite nonnegative family with a vector of positive mass
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.24, (3.23), p.43 (PDF p.45); proof pp.77–86 (PDF pp.79–88); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_hbar
import Definitions.Def_FairFacilityLoc_tau
import Definitions.Def_FairFacilityLoc_share
import Definitions.Def_FairFacilityLoc_IsNormalized

namespace FairFacilityLoc

/-- **Proposition 3.24** (Yan, Zhou, manuscript, sha256 642a1268…, p.43, PDF p.45; proof pp.77–86, PDF pp.79–88). For
`d ∈ {2, 3}`, if `C > d`, every coordinate with `z_r > τ_d` satisfies the bound (3.23),
`s_r < d z_r² − (d z_r² − 1) ω(v_r)` with `v_r = √((1 − z_r²)/(d − 1))`.

**Formalization Note.** Stated for weight families in normalized coordinates, as on p.49; `CapacityCondition` is the
conclusion of Lemma 3.9. -/
theorem proposition_3_24 {n d : ℕ} (hd : d = 2 ∨ d = 3) {W : Finset (Fin n → ℝ)} {x : Fin n → GeoSemialgCSP.E d}
    {z : GeoSemialgCSP.E d} (hN : IsNormalized W x z) (hC : CapacityCondition (penalty d) W x)
    (hCd : (d : ℝ) < weightedCapacity (penalty d) W x z) (r : Fin d) (hr : tau d < z r) :
    share (penalty d) W x z r <
      (d : ℝ) * z r ^ 2 -
        ((d : ℝ) * z r ^ 2 - 1) * omegaFun d (penalty d) (vCoord d (z r)) := by sorry

end FairFacilityLoc
