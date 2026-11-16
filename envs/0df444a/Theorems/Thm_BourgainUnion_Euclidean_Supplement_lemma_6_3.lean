-- Prove2me | Theorems.Thm_BourgainUnion_Euclidean_Supplement_lemma_6_3
-- name    : BourgainUnion.Euclidean.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:37:31.217201+00:00
-- url     : https://prove2.me/theorems/118ecded-1729-4d76-9501-4def4eea3df8
-- title:
--   Lemma 6.3 — the extension constant of the cube layer
-- statement:
--   Let $m\ge1$ be an integer, $r>0$, $s=\sqrt{r^2+1}-r$, and give the two-layer cube $X_m$ the metric (22). Then the Lipschitz extension constant of the layer $A$ in $X_m$ satisfies
--   $$e(A)\ge\frac{\sqrt m}{2r+s\sqrt m}.$$
--   Here $e(A)$ is the least $\Lambda\ge1$ such that every Lipschitz map $f:A\to\ell_2$ extends to $F:X_m\to\ell_2$ with $\mathrm{Lip}(F)\le\Lambda\,\mathrm{Lip}(f)$.
--
--   Differences from the source:
--   - encoding: e(A) for the metric (22) on X_m → the published extensionConstant of layerA m, for every metric instance on X_m whose distance equals (22); reason: extensionConstant depends only on the distance; such an instance exists by Lemma 6.2
--   - encoding: the standing m ≥ 1 and r > 0 of (22) and Lemma 6.2 → hypotheses 1 ≤ m and 0 < r; reason: the setting in which (22) is defined
--   - encoding: e(A) → the same quantity in ℝ≥0∞ (⊤ when no finite constant exists); reason: infinite values are representable, so no finiteness is assumed and no real-infimum default 0 arises
--   - encoding: real ℓ₂ → square-summable real sequences H2 = lp (fun _ : ℕ => ℝ) 2; reason: H2 is real ℓ₂, the published target of the base mission
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 26, §6.2, Lemma 6.3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_ExtensionModel
import Definitions.Def_BourgainUnion_Euclidean_Supplement_CubeModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Lemma 6.3, p. 26: for any metric structure on `X_m` whose distance is (22),
`e(A) ≥ √m / (2r + s√m)`. -/
theorem lemma_6_3 (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 < r) [MetricSpace (Cube m)]
    (hd : ∀ x y : Cube m, dist x y = cubeDist m r x y) :
    ENNReal.ofReal (Real.sqrt m / (2 * r + cubeS r * Real.sqrt m)) ≤
      extensionConstant (layerA m) := by sorry

end BourgainUnion.Euclidean.Supplement
