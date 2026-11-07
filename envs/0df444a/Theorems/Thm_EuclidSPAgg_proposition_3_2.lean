-- Prove2me | Theorems.Thm_EuclidSPAgg_proposition_3_2
-- name    : EuclidSPAgg.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:32.744361+00:00
-- url     : https://prove2.me/theorems/7bc65f03-8f06-40f6-b9fd-0417e07097bf
-- title:
--   Proposition 3.2 — the absorbing mechanism $g$ on $n-2$ reports exists, is unique, and inherits the properties of $f$
-- statement:
--   Let $n\ge3$ and let $f:E^n\to E$ be anonymous, continuous and strategyproof, with every unilateral menu compact. Then:
--
--   1. there is a unique map $g:E^{n-2}\to E$ satisfying
--   $$
--   f(a,g(z),z)=g(z)\qquad(a\in E,\ z\in E^{n-2});
--   $$
--   2. this $g$ is anonymous, continuous and strategyproof;
--   3. if $f$ is also normalized and unanimous, then so is $g$.
--
--   The absorbing mechanism is the population-reduction step of the structural induction: it replaces a mechanism on $n$ reports by one on $n-2$ reports.
--
--   **Formalization Note** $n=m+2$ with $m\ge1$. Parts 2 and 3 are stated for every $g$ satisfying the identity, which by part 1 is the unique one.
--
--   Differences from the source:
--   - encoding: n ≥ 3, g : E^{n−2} → E → n = m + 2 with 1 ≤ m, g : Mech m d; reason: the same range of population sizes
--   - encoding: the map g → every g with Absorbs f g; reason: by the uniqueness clause there is exactly one such g
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Proposition 3.2, display (3.1), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EuclidSPAgg_IsStrategyproof
import Definitions.Def_EuclidSPAgg_IsAnonymous
import Definitions.Def_EuclidSPAgg_IsUnanimous
import Definitions.Def_EuclidSPAgg_IsNormalized
import Definitions.Def_EuclidSPAgg_menu
import Definitions.Def_EuclidSPAgg_Absorbs
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Proposition 3.2** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.13 (PDF p.15)). Let `n ≥ 3`, and let `f : Eⁿ → E` be anonymous,
continuous and strategyproof with compact unilateral menus. There is a unique map
`g : E^{n−2} → E` with `f(a, g(z), z) = g(z)` for all `a ∈ E`, `z ∈ E^{n−2}` (display (3.1)).
The map `g` is anonymous, continuous and strategyproof. If `f` is also normalized and unanimous,
then so is `g`.

**Formalization Note** `n = m + 2` with `m ≥ 1`. The second part is stated for every `g`
satisfying (3.1), which by the first part is the unique one. `d ≥ 1` is standing (p.8). -/
theorem proposition_3_2 (m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) (f : Mech (m + 2) d)
    (hA : IsAnonymous f) (hC : Continuous f) (hSP : IsStrategyproof f)
    (hK : ∀ (i : Fin (m + 2)) (x : Fin (m + 2) → E d), IsCompact (menu f i x)) :
    (∃! g : Mech m d, Absorbs f g) ∧
      ∀ g : Mech m d, Absorbs f g →
        IsAnonymous g ∧ Continuous g ∧ IsStrategyproof g ∧
          (IsNormalized f → IsUnanimous f → IsNormalized g ∧ IsUnanimous g) := by sorry

end EuclidSPAgg
