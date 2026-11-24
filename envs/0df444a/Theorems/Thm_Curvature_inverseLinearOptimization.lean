-- Prove2me | Theorems.Thm_Curvature_inverseLinearOptimization
-- name    : Curvature.inverseLinearOptimization
-- status  : Proved
-- author  : @ssakaue
-- created : 2026-11-24T07:27:44.986341+00:00
-- url     : https://prove2.me/theorems/a88d832b-8d9d-4263-8cdc-991b1a02fcd8
-- title:
--   Corollary 8 — online inverse linear optimization relative to the observed actions
-- statement:
--   Let $\mathcal K\subset\mathbb R^d$ be a nonempty compact convex set, and let $\omega_{\psi_1}(\mathcal K)$ be its maximal subexponential mean width, the supremum of $\mathbb E\sup_{w\in\mathcal K}\langle Z,w\rangle$ over random vectors $Z$ in $\mathbb R^d$ with $\mathbb EZ=0$ and $\mathbb E\exp|\langle v,Z\rangle|\le2$ for every $v\in\mathbb B_2^d$. Fix one of the two domain initializations for Algorithm 4 in the formalization of Theorem 6. The first uses an admissible description with representation cost at most $2048\,\omega_{\psi_1}(\mathcal K)$. The second uses a representation of $\mathcal K$ as the image of a unit $\ell_p$ ball with $p\ge2$ under an affine map with orthogonal nonzero columns, together with a choice of fixed initial diagonal. Let $G,W>0$ satisfy $\omega_{\psi_1}(\mathcal K)\le W$, and fix a weight rule for Algorithm 5 that satisfies the paper's approximation condition for the scale $M=2GW/\log2$.
--
--   In round $t=1,2,\ldots$, the learner receives an action set $\mathcal X_t\subset\mathbb R^d$, a nonempty compact set with $\lVert a-b\rVert_2\le G$ for all $a,b\in\mathcal X_t$. Algorithm 5, run with $G$ and $W$ on the inputs $\widehat a_s-y_s$ of the earlier rounds $s<t$, supplies the utility estimate $w_t\in\mathcal K$. After seeing $\mathcal X_t$, the learner recommends an action $\widehat a_t\in\mathcal X_t$ with $\langle w_t,b\rangle\le\langle w_t,\widehat a_t\rangle$ for all $b\in\mathcal X_t$, and then observes an action $y_t\in\mathcal X_t$ taken by the user. The observed actions may be any points of the action sets and are not assumed to be optimal for any vector.
--
--   For $u\in\mathcal K$ and $T\ge1$, define the cumulative utility that the observed actions forgo under $u$ and the regret of the recommendations relative to the observed actions by
--
--   $$
--   D_T(u)\coloneqq\sum_{t=1}^T\max_{a\in\mathcal X_t}\langle u,a-y_t\rangle
--   \quad\text{and}\quad
--   R_T^{\mathrm{obs}}(u)\coloneqq\sum_{t=1}^T\langle u,y_t-\widehat a_t\rangle.
--   $$
--
--   Then, with $C\coloneqq24\bigl(393216+514/\log2\bigr)$, for every $u\in\mathcal K$ and every $T\ge1$,
--
--   $$
--   R_T^{\mathrm{obs}}(u)\le C\Bigl(GW+\sqrt{GW\,D_T(u)}\Bigr).
--   $$
--
--   The bound holds for every $u\in\mathcal K$, in particular for the user's unknown utility vector. The quantity $R_T^{\mathrm{obs}}(u)$ is signed: it is positive when the observed actions have more utility under $u$ than the recommendations, and the inequality bounds it from above. If every observed action is optimal in its action set for $u$, then $D_T(u)=0$ and the bound $CGW$ does not grow with $T$. In Corollary 8, $\lesssim$ leaves the multiplicative factor in this upper bound implicit. The Lean statement uses $C$ for that factor.
-- source:
--   arXiv:2611.27572v1, Corollary 8, p. 15. https://arxiv.org/html/2611.27572v1#Thmtheorem8

import Definitions.Def_Curvature_AdaptivePredictor
import Definitions.Def_Curvature_InverseLinearActions

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}
variable {G W : ℝ}
variable (I : DomainInitialization K) (hc : IsCompact K) (hcv : Convex ℝ K) (hne : K.Nonempty)
  (P : AdaptiveWeightRule (adaptiveWidthScale G W))

theorem Curvature.inverseLinearOptimization (hG : 0 < G) (hW : 0 < W) (hw : coordinateWidth K ≤ W)
    (X : ℕ → InverseLinearActions d G) (a y : ℕ → Vec d)
    (hy : ∀ t, y t ∈ (X t).carrier)
    (ha : ∀ t, (X t).Optimal (inverseLinearPredict I hc hcv hne P t
      (fun j => a j.val - y j.val)).val (a t))
    (T : ℕ) (hT : 0 < T) (u : K) :
    let D := ∑ t ∈ Finset.range T, (X t).shortfall u.val (y t)
    (∑ t ∈ Finset.range T, dotProduct u.val (y t-a t)) ≤
      adaptiveWidthConstant*(G*W + Real.sqrt (G*W*D)) := by sorry
