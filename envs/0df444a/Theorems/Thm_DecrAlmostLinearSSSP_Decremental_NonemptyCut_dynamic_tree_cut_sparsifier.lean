-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_NonemptyCut_dynamic_tree_cut_sparsifier
-- name    : DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_tree_cut_sparsifier
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:47.652027+00:00
-- url     : https://prove2.me/theorems/32fca2cf-5569-4158-8012-8e4ea9dd7427
-- title:
--   Deterministic normalized tree-cut sparsifier with charged exact detection
-- statement:
--   For every fixed numerical-range exponent $d$, there is one deterministic online scalar-RAM tree-cut implementation, a constant $C>0$, and positive subpolynomial functions $K,h,a$. Writing $L=\log\max\{2,m\}$, its approximation factor satisfies
--   $$
--   K(m)\le 2^{C L^{5/6}\max\{1,\log L\}}.
--   $$
--
--   On every nonempty connected physical multigraph whose active capacities lie in $[1,\max\{2,m\}^{2d}]$ and whose zero-sum demands are bounded by $\max\{2,m\}^d$, the implementation maintains edge updates, paired demand changes, approximately minimum-ratio implicit cuts, lazy cut toggles and implicit vertex potentials. For every nonzero-demand refresh, the returned $(G,U,C)$ satisfies
--   $$
--   G<0<U,\qquad G=\gamma(C),\qquad \operatorname{cap}_u(C)\le U,\qquad
--   \frac GU\le \frac{\gamma\cdot x}{K(m)\,\|x\|_u}
--   $$
--   for every direction $x$ with $\|x\|_u>0$.
--
--   In addition, charged private `peek` and `reset` operations give an exact output-sensitive detector: `peek` either returns an active edge at or above threshold $\xi>0$ or certifies that none exists, and `reset` recalibrates exactly one active edge. Initialization costs at most $Cma(m)$, and total work is initialization plus at most $h(m)$ per public or private operation. The cut and potential remain implicit; no linear-size decoding or uncharged semantic evaluator is available.
--
--   This isolates the deterministic dynamic capacitated expander-hierarchy/tree-cut ingredient from the public scaling and report-draining wrapper.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, STOC 2027 submission #912, p.9, Lemma 3.2 (adapted from van den Brand et al., Theorem 5.4), and p.16 numerical-range convention; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf. Normalized operational form with lazy ToggleCut and exact output-sensitive detector primitives, as defined in DecrAlmostLinearSSSP_TreeCutProtocol.

import Definitions.Def_DecrAlmostLinearSSSP_TreeCutProtocol

set_option autoImplicit false
open scoped ENNReal NNReal

/-- External deterministic dynamic tree-cut sparsifier with lazy toggles and exact
charged detector primitives on the normalized numerical range. -/
theorem DecrAlmostLinearSSSP.Decremental.NonemptyCut.dynamic_tree_cut_sparsifier :
    ∀ exponent : ℕ, ∃ (impl : TreeImplementation) (K h a : ℕ → ℝ) (C : ℝ),
      0 < C ∧ Subpolynomial K ∧ Subpolynomial h ∧ Subpolynomial a ∧
      (∀ m, K m ≤ Real.rpow 2
        (C * Real.rpow (Real.log (max 2 m : ℕ)) (5 / 6 : ℝ) *
          max 1 (Real.log (Real.log (max 2 m : ℕ))))) ∧
      ∀ m ξ, 0 < ξ → TreeImplements impl m exponent (K m) (h m)
        (C * m * a m) ξ := by sorry
