-- Prove2me | Theorems.Thm_AssetDebt_ControlBand_lemma_3
-- name    : AssetDebt.ControlBand.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:14:06.209984+00:00
-- url     : https://prove2.me/theorems/c26de9bd-290b-44d0-95ca-02a060c49266
-- title:
--   Lemma 3, p. 13 — single payment at $m < T$: $V_t$ is convex in $(x_t, w_t, d_m)$ for $w_t \le \rho^{m-t} d_m$, linear for $w_t \ge \rho^{m-t} d_m$, and continuous
-- statement:
--   Assume no capacity constraint ($\ell = 1$) and a single debt payment $d_m$ due at the end of period $m$, with $1 \le m < T$. Fix a period $1 \le t \le m$ and a price $p > 0$, and regard the equity value $V_t(x, w, p; d)$ as a function of the triple $(x, w, d_m)$ with $x \in [0,1]$, $w \ge 0$, $d_m \ge 0$. Then:
--
--   1. $V_t$ is **convex** in $(x, w, d_m)$ on the region $w \le \rho^{m-t} d_m$;
--   2. $V_t$ is **linear** in $(x, w, d_m)$ on the region $w \ge \rho^{m-t} d_m$: there are constants $a, b, c$ (depending on $t$ and $p$) with $V_t = a\,x + b\,w + c\,d_m$ there;
--   3. $V_t$ is **continuous** in $(x, w, d_m)$.
--
--   The convexity in the first region is what limits the optimal first sale to three candidate quantities in the proof of Proposition 4; the debt level $d_m$ is included among the variables because the effect of debt is studied by varying it.
--
--   **Formalization Note** The debt amount varies through the single-payment schedule $d_m = D$, $d_t = 0$ for $t \ne m$. "Linear" is rendered as the existence of coefficients with no constant term, which is what the paper's proof gives.
-- source:
--   Ahn, Wang & Wu, Asset Selling Under Debt Obligations, SSRN 3472345 (version of May 7, 2019), p. 13 (PDF 13), Lemma 3

import Mathlib
import Definitions.Def_AssetDebt_ControlBand_Model

namespace AssetDebt.ControlBand

open MeasureTheory ProbabilityTheory

/-- Lemma 3, p. 13: under a single payment `d_m = D` at `m < T` and `ℓ = 1`, for `t ≤ m`,
`V_t(x, w, p; d)` is convex in `(x, w, d_m)` on the region `w ≤ ρ^{m-t} d_m`, linear in
`(x, w, d_m)` on the region `w ≥ ρ^{m-t} d_m`, and continuous in `(x, w, d_m)`.
A point `v = (x, w, D)` ranges over `x ∈ [0, 1]`, `w ≥ 0`, `D ≥ 0`. -/
theorem lemma_3 (P : Params) (hS : P.Standing) (hℓ : P.ℓ = 1)
    (m : ℕ) (hm : 1 ≤ m ∧ m < P.T) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ m) (p : ℝ) (hp : 0 < p) :
    ConvexOn ℝ
        {v : ℝ × ℝ × ℝ | 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2 ∧
          v.2.1 ≤ P.ρ ^ (m - t) * v.2.2}
        (fun v : ℝ × ℝ × ℝ => V P (singlePayment m v.2.2) m t v.1 v.2.1 p) ∧
    (∃ a b c : ℝ, ∀ v : ℝ × ℝ × ℝ, 0 ≤ v.1 → v.1 ≤ 1 → 0 ≤ v.2.1 → 0 ≤ v.2.2 →
        P.ρ ^ (m - t) * v.2.2 ≤ v.2.1 →
        V P (singlePayment m v.2.2) m t v.1 v.2.1 p = a * v.1 + b * v.2.1 + c * v.2.2) ∧
    ContinuousOn (fun v : ℝ × ℝ × ℝ => V P (singlePayment m v.2.2) m t v.1 v.2.1 p)
        {v : ℝ × ℝ × ℝ | 0 ≤ v.1 ∧ v.1 ≤ 1 ∧ 0 ≤ v.2.1 ∧ 0 ≤ v.2.2} := by sorry

end AssetDebt.ControlBand
