-- Prove2me | Theorems.Thm_Curvature_adaptiveWidth
-- name    : Curvature.adaptiveWidth
-- status  : Open
-- author  : @ssakaue
-- created : 2026-11-24T07:23:53.927933+00:00
-- url     : https://prove2.me/theorems/c2198591-2461-427a-a8ab-f1a15f02952f
-- title:
--   Theorem 1 — small-loss regret of Algorithm 5 on every compact convex domain
-- statement:
--   Let $\mathcal K\subset\mathbb R^d$ be a nonempty compact convex set, and let $\omega_{\psi_1}(\mathcal K)$ be its maximal subexponential mean width, the supremum of $\mathbb E\sup_{w\in\mathcal K}\langle Z,w\rangle$ over random vectors $Z$ in $\mathbb R^d$ with $\mathbb EZ=0$ and $\mathbb E\exp|\langle v,Z\rangle|\le2$ for every $v\in\mathbb B_2^d$. Fix one of the two domain initializations for Algorithm 4 in the formalization of Theorem 6. The first uses an admissible description of $\mathcal K$ with representation cost at most $2048\,\omega_{\psi_1}(\mathcal K)$. The second uses a representation of $\mathcal K$ as the image of a unit $\ell_p$ ball with $p\ge2$ under an affine map with orthogonal nonzero columns, together with a choice of fixed initial diagonal. By Proposition 9 of the paper, an initialization of the first kind exists whenever $\mathcal K$ has at least two points. Let $G,W>0$ satisfy $\omega_{\psi_1}(\mathcal K)\le W$, and let $g_1,g_2,\ldots\in\mathbb R^d$ be arbitrary vectors with $\lVert g_t\rVert_2\le G$.
--
--   Run Algorithm 5 of the paper with $G$, $W$ and any weight rule that satisfies the paper's approximation condition for the scale $M=2GW/\log2$; the exact weights are one such rule. Algorithm 5 is deterministic. Its base learner $i=0,1,2,\ldots$ runs Algorithm 4 with the given initialization and the parameter $\varepsilon_i=2^{-i}/8$ from round $2^i$ on and receives rescaled inputs. In round $t$, Algorithm 5 predicts a weighted average $w_t\in\mathcal K$ of the predictions of the active base learners, then observes $g_t$, and then updates the base learners and their cumulative losses. Thus $w_t$ depends only on $g_1,\ldots,g_{t-1}$.
--
--   Let $C\coloneqq24\bigl(393216+514/\log2\bigr)$, and for $u\in\mathcal K$ and $T\ge1$ write
--
--   $$
--   R_T^{\mathrm{lin}}(u)\coloneqq\sum_{t=1}^T\langle g_t,w_t-u\rangle
--   \quad\text{and}\quad
--   N_T(u)\coloneqq\sum_{t=1}^T\max\{\langle g_t,u-w_t\rangle,0\}.
--   $$
--
--   Then, with one prediction sequence $(w_t)$ for all $u\in\mathcal K$ and all $T\ge1$, the following hold.
--
--   1. For arbitrary inputs as above,
--   $$
--   R_T^{\mathrm{lin}}(u)\le C\Bigl(GW+\sqrt{GW\,N_T(u)}\Bigr).
--   $$
--   2. Let $f_1,\ldots,f_T\colon\mathbb R^d\to\mathbb R$ be functions that are continuous on $\mathcal K$ and satisfy $f_t(w_t)-f_t(v)\le\langle g_t,w_t-v\rangle$ for all $v\in\mathcal K$, as they do when $g_t$ is a subgradient of a convex loss $f_t$ at $w_t$. Define the regret $R_T(u)\coloneqq\sum_{t=1}^T\bigl(f_t(w_t)-f_t(u)\bigr)$ and the shifted comparator loss
--   $$
--   \Delta_T(u)\coloneqq\sum_{t=1}^T\Bigl(f_t(u)-\min_{w\in\mathcal K}f_t(w)\Bigr).
--   $$
--   Then
--   $$
--   R_T(u)\le R_T^{\mathrm{lin}}(u)\le C\Bigl(GW+\sqrt{GW\,N_T(u)}\Bigr)\le C\Bigl(GW+\sqrt{GW\,\Delta_T(u)}\Bigr).
--   $$
--
--   The quantity $\Delta_T(u)$ is the comparator's cumulative loss above the per-round minima; it equals the comparator's cumulative loss when every per-round minimum is zero. The paper states the bound with a universal constant $c$ in place of $C$.
-- source:
--   arXiv:2611.27572v1, Theorem 1, p. 2. https://arxiv.org/html/2611.27572v1#Thmtheorem1

import Definitions.Def_Curvature_AdaptivePredictor

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}

theorem Curvature.adaptiveWidth (init : DomainInitialization K) (hc : IsCompact K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K) :
    let w := (init.adaptiveBase hne hc hcv).adaptivePlay hcv P G g
    let r := fun t => excess (g t) (w t).val u.val
    let n := adaptiveNegative T r
    let rhs := adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n))
    (∑ t ∈ Finset.range T, r t) ≤ rhs ∧
      ∀ (f : ℕ → Vec d → ℝ), (∀ t < T, ContinuousOn (f t) K) →
        (∀ t < T, ∀ v ∈ K, f t (w t).val - f t v ≤ excess (g t) (w t).val v) →
        let Δ := ∑ t ∈ Finset.range T, (f t u.val - sInf (f t '' K))
        (∑ t ∈ Finset.range T, (f t (w t).val - f t u.val)) ≤ (∑ t ∈ Finset.range T, r t) ∧
          rhs ≤ adaptiveWidthConstant*(G*W+Real.sqrt (G*W*Δ)) := by sorry
