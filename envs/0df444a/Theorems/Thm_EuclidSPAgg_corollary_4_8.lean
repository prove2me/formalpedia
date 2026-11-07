-- Prove2me | Theorems.Thm_EuclidSPAgg_corollary_4_8
-- name    : EuclidSPAgg.corollary_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:09.237198+00:00
-- url     : https://prove2.me/theorems/38570cc3-14ae-4f8a-8d67-353343716031
-- title:
--   Corollary 4.8 — every unilateral menu of the absorbing mechanism is an orthogonal box
-- statement:
--   Let $n\ge3$, let $f:E^n\to E$ be anonymous, continuous and strategyproof with compact unilateral menus, and let $g:E^{n-2}\to E$ be its absorbing mechanism from Proposition 3.2, i.e. $f(a,g(z),z)=g(z)$ for all $a\in E$, $z\in E^{n-2}$. Then every unilateral menu of $g$ is an orthogonal box. The frame of the box may depend on the agent and on the outside profile.
--
--   This supplies the box-shaped menus that Theorem 6.5 needs for the smaller mechanism.
--
--   Differences from the source:
--   - reading: the absorbing mechanism in Proposition 3.2 → any g with f(a, g(z), z) = g(z), for f satisfying the hypotheses of Proposition 3.2 (n = m + 2, m ≥ 1); reason: the corollary refers to Proposition 3.2's setting, where this g is unique
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Corollary 4.8, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_EuclidSPAgg_Absorbs
import Definitions.Def_EuclidSPAgg_IsOrthogonalBox
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Corollary 4.8** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.23 (PDF p.25)). Every unilateral menu of the absorbing mechanism in
Proposition 3.2 is an orthogonal box. The frame may depend on the outside profile.

**Formalization Note** The hypotheses are those of Proposition 3.2 on `f` (`n = m + 2 ≥ 3`;
anonymous, continuous, strategyproof, compact unilateral menus), and `g` satisfies the absorbing
identity (3.1). The frame is inside `IsOrthogonalBox`, so it may depend on the agent `i` and the
outside reports. `d ≥ 1` is standing (p.8). -/
theorem corollary_4_8 (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (f : Mech (m + 2) d)
    (hA : IsAnonymous f) (hC : Continuous f) (hSP : IsStrategyproof f)
    (hK : ∀ (i : Fin (m + 2)) (x : Fin (m + 2) → E d), IsCompact (menu f i x))
    (g : Mech m d) (hg : Absorbs f g) :
    ∀ (i : Fin m) (z : Fin m → E d), IsOrthogonalBox (menu g i z) := by sorry

end EuclidSPAgg
