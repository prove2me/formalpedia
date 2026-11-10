-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_weight_rounding
-- name    : EdgeSublinearMWIS.Main.weight_rounding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:09.798354+00:00
-- url     : https://prove2.me/theorems/e9a5fde3-2171-4449-8863-56a0291b96ce
-- title:
--   The weight-rounding inequalities in the weighted reduction
-- statement:
--   Let $G$ have $n\ge2$ vertices and nonnegative rational weights $w$ with $w_{\max}>0$, and let rational $0<\varepsilon<1$. The actual guarded rounding routine returns
--   $$\tau=\varepsilon w_{\max}/(2n)>0,\qquad t_v=\lfloor w_v/\tau\rfloor,\qquad \sum_vt_v\le2n^2/\varepsilon.$$
--   For its explicitly labeled rounded graph $G'$, omitting zero fibers, the source's comparisons hold:
--   $$(1-\varepsilon/2)\alpha_w(G)\le\tau\alpha(G'),\qquad \tau|I'|\le w(I).$$
--   The second inequality holds for every independent set $I'$ of $G'$, with $I$ the set of its original owners; this $I$ is independent in $G$. Both comparisons and the precise scale and copy bound are included. This supporting target records the p.20 reduction; it is not an additional milestone or a restriction of the signed-weight goal.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: copies of each original vertex, omitting zero fibers → prefix-count ownership on Fin(totalCopies) and an explicit return map; reason: a deterministic labeling avoids arbitrary relabeling choice and preserves exactly the source blow-up
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §6, Theorem 2 proof, scale, copy bound and weight comparisons, p.20 (PDF p.20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- The exact scale, copy bound and both weight comparisons in the p.20 proof.
Zero fibers are omitted by the prefix-count graph construction. -/
theorem weight_rounding {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℚ) (ε : ℚ)
    (hn : 2 ≤ n) (hw : ∀ v, 0 ≤ w v) (hmax : 0 < maximumWeight w)
    (he : 0 < ε) (he1 : ε < 1) :
    ∃ (τ : ℚ) (t : Fin n → ℕ), weightRounding w ε = some (τ, t) ∧
      0 < τ ∧ τ = ε * maximumWeight w / (2 * (n : ℚ)) ∧
      (∀ v, t v = ⌊w v / τ⌋₊) ∧
      (totalCopies t : ℚ) ≤ 2 * (n : ℚ) ^ 2 / ε ∧
      (1 - (ε : ℝ) / 2) * weightedAlpha G w ≤
        (τ : ℝ) * alpha (roundedGraph G t) Finset.univ ∧
      ∀ I : Finset (Fin (totalCopies t)),
        (roundedGraph G t).IsIndepSet (I : Set (Fin (totalCopies t))) →
        G.IsIndepSet (originalVertices t I : Set (Fin n)) ∧
        (τ : ℝ) * I.card ≤ ∑ v ∈ originalVertices t I, (w v : ℝ) := by sorry

end EdgeSublinearMWIS.Main
