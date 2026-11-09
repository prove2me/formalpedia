-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_dimension_bound_under_expansion
-- name    : BinaryThreeLCC.Main.dimension_bound_under_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:03:04.767259+00:00
-- url     : https://prove2.me/theorems/a9357f9d-8af7-42a5-a281-347f077746a3
-- title:
--   Lemma 4.1 — dimension under edge expansion (corrected: singleton bound)
-- statement:
--   Let $\Omega,\Lambda$ be nonempty finite sets of sizes $m,n$, and let $v:\Omega\to W$ and $w:\Lambda\to W$ label them in any vector space $W$ over $\mathbb F_2$. Let $\mathcal H$ consist of tuples $(u,\{a,b\},u')$, with $a\ne b$, with at most one tuple using a given pair $(u,a)$. Assume
--
--   $$v_u+w_a+w_b+v_{u'}=0\qquad((u,\{a,b\},u')\in\mathcal H).$$
--
--   The directed graph $D_{\mathcal H}$ has one edge copy $u\to u'$ per tuple. If it is Eulerian and $\lambda$-cut-dense for $\lambda>0$, then
--
--   $$\dim\operatorname{span}\{v_u:u\in\Omega\}\le
--   \max\left\{1,\frac{4096n^2}{\lambda^2m^2}\log_2 m\log_2 n\right\}.$$
--
--   The ambient space need not be finite dimensional. The two finite index sets are independent; the only finite dimension measured is that of the span of $v$.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - correction: an O(n² log m log n/(λ²m²)) bound that vanishes at m=1 → max{1,4096 n² log₂m log₂n/(λ²m²)}; reason: Ω singleton, Λ of size two, W=F₂, v=1, w=0, H empty and λ=1 satisfy the printed assumptions but have dimension one
--   - encoding: an absolute implicit O constant and positive expansion/defined logarithms → constant 4096, nonempty Ω and Λ, and λ > 0; reason: the proof on printed pp.13–17 gives at most 2100 in the nonsingleton regime; the max repairs only the singleton regime
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Lemma 4.1, printed p. 10, PDF p. 12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_Matchings
import Definitions.Def_BinaryThreeLCC_Main_TupleSystem

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Lemma 4.1. The max with one repairs its false singleton case. The ambient
space is arbitrary; only the span of the finitely many labels is measured. -/
theorem dimension_bound_under_expansion {Ω Λ : Type} [Fintype Ω] [Fintype Λ]
    [Nonempty Ω] [Nonempty Λ] {W : Type*} [AddCommGroup W] [Module Bit W]
    (H : TupleSystem Ω Λ) (v : Ω → W) (w : Λ → W) (hparity : TupleParity H v w)
    (lam : ℝ) (hlam : 0 < lam) (hEuler : Eulerian (tupleGraph H))
    (hcut : CutDense (tupleGraph H) lam) :
    (spanDimension v : ℝ) ≤ max 1
      (4096 * (Fintype.card Λ : ℝ) ^ 2 / (lam ^ 2 * (Fintype.card Ω : ℝ) ^ 2) *
        Real.logb 2 (Fintype.card Ω) * Real.logb 2 (Fintype.card Λ)) := by sorry

end BinaryThreeLCC.Main
