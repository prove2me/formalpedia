-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_14
-- name    : AutobidSPPE.lemma_2_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:03:37.225116+00:00
-- url     : https://prove2.me/theorems/91d44e6a-1588-46a0-b4d2-5eb7fb997abe
-- title:
--   Lemma 2.14 — uniform Lipschitz bound for conditional equilibria
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. For $k\in\{1,\dots,n-1\}$ and later endpoints $v,w\in\prod_{j>k}[\underline y_j,\bar v_j]$, the conditional equilibria of bidders $1,\dots,k$ satisfy
--   $$
--   \|p^{[k]}(v)-p^{[k]}(w)\|_\infty\le L_p\,\|v-w\|_\infty ,\qquad L_p=2/\underline\gamma .
--   $$
--   The bound holds across weakly binding caps and changes of the binding set.
--
--   **Formalization Note** Stated for any two conditional equilibria of the prefix $[k]$ (indices $<k$): their prefixes are within $L_p$ times the distance of their suffixes.
--
--   Differences from the source:
--   - encoding: the conditional equilibrium p^[k](v) → any full profile z with IsCondEq k z whose later coordinates equal v; reason: such z exists and is unique (Lemma 2.11), so quantifying over all of them states the same fact
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.14, p.19

import Mathlib
import Definitions.Def_AutobidSPPE_IsCondEq
import Definitions.Def_AutobidSPPE_Lp

namespace AutobidSPPE

/-- Lemma 2.14, p.19 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): for `k ∈ {1, …, n−1}` the conditional equilibrium endpoints
`p^[k](v)` of bidders `1, …, k` with later endpoints `v ∈ ∏_{j>k}[y̲ⱼ, v̄ⱼ]` satisfy
`‖p^[k](v) − p^[k](w)‖_∞ ≤ L_p ‖v − w‖_∞`.

**Formalization Note** Two conditional equilibria `y`, `z` of the same prefix (`IsCondEq k`) are
compared: their prefixes (indices `j.val < k`) are at sup distance at most `L_p` times the sup
distance of their suffixes (indices `k ≤ j.val`). -/
theorem lemma_2_14 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i) :
    ∀ k : ℕ, 1 ≤ k → k < n → ∀ y z : Fin n → ℝ, IsCondEq vbar ρ k y → IsCondEq vbar ρ k z →
      ‖fun j : {j : Fin n // j.val < k} => y j - z j‖ ≤
        Lp vhat ρ * ‖fun j : {j : Fin n // k ≤ j.val} => y j - z j‖ := by sorry

end AutobidSPPE
