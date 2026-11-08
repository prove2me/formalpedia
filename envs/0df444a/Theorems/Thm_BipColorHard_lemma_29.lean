-- Prove2me | Theorems.Thm_BipColorHard_lemma_29
-- name    : BipColorHard.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:34:27.135066+00:00
-- url     : https://prove2.me/theorems/925cd3fd-1e00-4325-92fc-a436f2704805
-- title:
--   Lemma 29 — at most three types; a three-type local maximum has middle multiplicity one
-- statement:
--   Let $q=2k+1\ge5$, $d=q$, $p=(d+1)/d$. Let $(P,R)$ be a stationary pair of $\Phi$. Then $(P,R)$ has at most three types. Suppose it has exactly three, and let $a,b,c$ be colors with $P_a>P_b>P_c$. Then
--   $$P_bR_b>P_aR_a,\qquad P_bR_b>P_cR_c,$$
--   and if $(P,R)$ is a local maximum of $\Phi$, then $b$ is the only color in its type.
--
--   This restricts the possible maximizers of $\Phi$ to a small family and is the starting point of the classification of phases.
--
--   Differences from the source:
--   - encoding: the middle type, in the order of the coordinates of $P$ → colors $a,b,c$ with $P_a>P_b>P_c$; reason: with three types these are representatives of the three types in order, p.33
--   - encoding: local maximum of $\Phi$ → local maximum in neighbourhoods of $\mathbb R^q\times\mathbb R^q$; reason: $\Phi$ is unchanged by positive scaling of either vector, so this agrees with local maximality under the normalizations
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Lemma 29, p.33 (PDF p.35); range of §7, p.30 (PDF p.32)

import Definitions.Def_BipColorHard_Objective

set_option autoImplicit false

namespace BipColorHard

/-- **Lemma 29**, p.33 (PDF p.35), Galanis, Guo, He, Štefankovič, Vigoda, manuscript of Nov. 3, 2026 (sha256
78a66d1f…). Range of §7, p.30 (PDF p.32): `q = 2k + 1 ≥ 5`, `d = q`, `p = (d + 1)/d`. Every stationary pair of `Φ`
has at most three types. If it has three, `P_i R_i` is strictly larger at the middle type than at either other
type, and such a pair is a local maximum of `Φ` only if its middle type contains exactly one color.

**Formalization Note.** Types are listed in decreasing order of the coordinates of `P` (p.33): when there are three
types, colors `a, b, c` with `P a > P b > P c` are representatives of the three types, in order, with `b` in the
middle. -/
theorem lemma_29 (k : ℕ) (hk : 2 ≤ k) (P R : Fin (2 * k + 1) → ℝ)
    (hst : IsStationary (2 * k + 1) P R) :
    typeCount P R ≤ 3 ∧
      (typeCount P R = 3 → ∀ a b c : Fin (2 * k + 1), P b < P a → P c < P b →
        P a * R a < P b * R b ∧ P c * R c < P b * R b ∧
          (IsLocalMaxPhi (2 * k + 1) P R → (Finset.univ.filter fun i => P i = P b).card = 1)) := by sorry

end BipColorHard
