-- Prove2me | Theorems.Thm_Curvature_fixedDomain
-- name    : Curvature.fixedDomain
-- status  : Open
-- author  : @ssakaue
-- created : 2026-11-24T07:23:39.507747+00:00
-- url     : https://prove2.me/theorems/d13a6f46-ce5c-4509-b254-7766ffeb05fd
-- title:
--   Theorem 6 — fixed-parameter guarantee for Algorithm 4 on a general compact convex domain
-- statement:
--   Let $\mathcal K\subset\mathbb R^d$ be a compact convex set with at least two points, let $G>0$ and $\varepsilon\in(0,1]$, and let $g_1,g_2,\ldots\in\mathbb R^d$ be arbitrary input vectors with $\lVert g_t\rVert_2\le G$. Let $\omega_{\psi_1}(\mathcal K)$ be the maximal subexponential mean width of $\mathcal K$, the supremum of $\mathbb E\sup_{w\in\mathcal K}\langle Z,w\rangle$ over random vectors $Z$ in $\mathbb R^d$ with $\mathbb EZ=0$ and $\mathbb E\exp|\langle v,Z\rangle|\le2$ for every $v\in\mathbb B_2^d$.
--
--   In the formalization, Algorithm 4 takes one of two kinds of domain initialization for $\mathcal K$. The first is an admissible description of $\mathcal K$, which writes every point of $\mathcal K$ as $w_\circ+Av$ with $v\in[-1,1]^N$ and fixes a length and a threshold for each of the $N$ coordinates. For each point of $\mathcal K$, take the minimum coefficient cost among the vectors $v$ that represent it. The supremum of these minima is the representation cost, which the formalization requires to be at most $2048\,\omega_{\psi_1}(\mathcal K)$. The second is a representation of $\mathcal K$ as the image of a unit $\ell_p$ ball with $p\ge2$ under an affine map with orthogonal nonzero columns, together with a choice of fixed initial diagonal. Fix such an initialization. By Proposition 9 of the paper, every compact convex set with at least two points has an admissible description with representation cost at most $20\,\omega_{\psi_1}(\mathcal K)$, so an initialization of the first kind always exists.
--
--   Run Algorithm 4 with this initialization, the bound $G$ and the parameter $\varepsilon$. In round $t$, it predicts the Euclidean projection $w_t\in\mathcal K$ of the point of $\mathbb R^d$ given by its internal iterate, then observes $g_t$, and then updates the internal iterate with the corrected and normalized input. Thus $w_t$ depends only on $g_1,\ldots,g_{t-1}$. Then, for every comparator $u\in\mathcal K$ and every horizon $T$,
--
--   $$
--   2\sum_{t=1}^T\langle g_t,w_t-u\rangle-\varepsilon\sum_{t=1}^T\bigl|\langle g_t,w_t-u\rangle\bigr|\le\frac{393216\,G}{\varepsilon}\,\omega_{\psi_1}(\mathcal K).
--   $$
--
--   The paper states this bound with a universal constant $c$ in place of $393216$. Because the inputs are arbitrary vectors rather than subgradients of losses, the bound applies to the rescaled inputs that Algorithm 5 sends to its base learners.
-- source:
--   arXiv:2611.27572v1, Theorem 6, p. 11. https://arxiv.org/html/2611.27572v1#Thmtheorem6

import Definitions.Def_Curvature_AdaptivePredictor
import Definitions.Def_Curvature_DomainGeometry
import Definitions.Def_Curvature_DyadicRun
import Definitions.Def_Curvature_FixedAxes
import Definitions.Def_Curvature_WidthAndSignGame
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}

theorem Curvature.fixedDomain (hc : IsCompact K) (hcv : Convex ℝ K) (hnon : K.Nontrivial)
    (I : DomainInitialization K) {G ε : ℝ} (hG : 0 < G) (hε : 0 < ε) (hε' : ε ≤ 1)
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (u : K) (T : ℕ) :
    let w := (I.adaptiveBase hnon.nonempty hc hcv).play G ε g
    let r := fun t => excess (g t) (w t).val u.val
    2*(∑ t ∈ Finset.range T, r t) - ε*(∑ t ∈ Finset.range T, |r t|) ≤
      (393216*G/ε)*coordinateWidth K := by sorry
