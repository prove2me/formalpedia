-- Prove2me | Theorems.Thm_DelayedGLCB_eq_41
-- name    : DelayedGLCB.eq_41
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:00.678332+00:00
-- url     : https://prove2.me/theorems/8357a002-b043-4967-9924-02b4ee5e481f
-- title:
--   (41) — the elliptical potential sum $\sum\|X_t\|_{V_t^{-1}}\le\sqrt{2dn\log((n+m)/d)}$
-- statement:
--   Let $d\ge1$, let $X_1,X_2,\dots$ be vectors in the unit ball of $\mathbb R^d$, $V_t=\sum_{s=1}^{t-1}X_sX_s'$, and let $m$ satisfy $\lambda_{\min}(V_{m+1})\ge1$. For every $n\ge0$,
--   $$
--   \sum_{t=m+1}^{m+n}\|X_t\|_{V_t^{-1}}\le\sqrt{2dn\log\Big(\frac{n+m}{d}\Big)}.
--   $$
--
--   Once the design matrix dominates the identity, the cumulative exploration widths grow like $\sqrt{dn\log n}$. Applied with $m=\tau$, this gives the $\sqrt{Td\log(T/d)}$ factor of the regret bound.
--
--   Differences from the source:
--   - generalization: X_t the features DUCB-GLCB plays → any sequence in the unit ball; reason: the bound uses only ‖X_t‖ ≤ 1 and λ_min(V_{m+1}) ≥ 1
--   - encoding: λ_min(A), the smallest eigenvalue → lambdaMin A, the infimum of v'Av over unit vectors; reason: equal for symmetric matrices, which are the only ones it is applied to
--   - encoding: V_t^{-1} → Matrix.inv; reason: V_t ⪰ V_{m+1} ⪰ I for t > m, so it is the true inverse
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, (41), pp.26–27

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_Vmat

namespace DelayedGLCB

open Matrix MostlyExplorationFree.GreedyBandit

/-- **Elliptical potential sum (41).**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, (41), pp.26–27: "Suppose there is an
integer `m` such that `λ_min(V_{m+1}) ≥ 1`, from Lemma 2 in [30], we have
`Σ_{t=m+1}^{m+n} ‖X_t‖_{V_t^{-1}} ≤ √(2dn log((n+m)/d))` (41) for all `n ≥ 0`."

For `d ≥ 1`, any vectors `X_1, X_2, …` in the unit ball of `ℝ^d` with `V_t = Σ_{s<t} X_sX_s'`, and any
`m` with `λ_min(V_{m+1}) ≥ 1`: for every `n ≥ 0`,
`Σ_{t=m+1}^{m+n} ‖X_t‖_{V_t^{-1}} ≤ √(2dn log((n+m)/d))`.

**Formalization Note.** The paper applies (41) to the features DUCB-GLCB plays; it holds for every
sequence in the unit ball, which is how it is stated. `λ_min` is `lambdaMin`, `V_t^{-1}` is
`Matrix.inv`. -/
theorem eq_41 (d : ℕ) (hd : 1 ≤ d) (X : ℕ → Fin d → ℝ) (hX : ∀ s, l2norm (X s) ≤ 1) (m : ℕ)
    (hm : 1 ≤ lambdaMin (Vmat X (m + 1))) (n : ℕ) :
    ∑ t ∈ Finset.Icc (m + 1) (m + n), wnorm (Vmat X t)⁻¹ (X t)
      ≤ Real.sqrt (2 * d * n * Real.log (((n : ℝ) + m) / d)) := by sorry

end DelayedGLCB
