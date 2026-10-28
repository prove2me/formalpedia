-- Prove2me | Theorems.Thm_BadLocalMin_Smooth_suboptimal_eq_43_50
-- name    : BadLocalMin.Smooth.suboptimal_eq_43_50
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T12:38:16.25699+00:00
-- url     : https://prove2.me/theorems/d058e9a9-4457-4b09-abe0-7309206ff35f
-- title:
--   §6.3, eqs. (43)–(50), pp. 23–24 — E(Θ) = ‖ΔY‖² > 0 and some Θ* has E(Θ*) < E(Θ)
-- statement:
--   Let $H \ge 1$ and $d_H \ge 2$, let $\Delta Y \in \mathbb R^{d_{H+1}\times N}$ be nonzero, and set $Y = \sigma(a)\mathbf 1 - \Delta Y$. Let $\Theta$ satisfy (19a)–(19e). Suppose some configuration $\Theta'$ makes the first neuron of the last hidden layer positively correlated with every row of $\Delta Y$:
--   $$\big\langle \Delta Y(i,:),\ (T_H)(1,:)(\Theta')\big\rangle > 0, \qquad 1 \le i \le d_{H+1} \qquad (44,\ j = 1).$$
--   Then
--   $$E(\Theta) = \|\Delta Y\|_F^2 > 0 \qquad (43)$$
--   and there is a configuration $\Theta^*$ with $E(\Theta^*) < E(\Theta)$ (50).
--
--   With Lemma 2's (33) supplying $\Theta'$ and (23d) giving $\Delta Y \ne 0$, this is §6.3: the local minimum of §6.2 is not a global minimum.
--
--   **Formalization Note.** Only the first neuron ($j = 1$, Lean index 0) of (44) is assumed, which is all the construction (45)–(48) uses. The printed (49c)–(49d) carry a sign slip in the cross term ($-2v$ instead of $+2v$); the conclusion $E(\Theta^*) < E(\Theta)$ is unaffected.
-- source:
--   Ding, Li & Sun, arXiv:1911.01413v3, pp. 23–24, §6.3, eqs. (43)–(50)

import Mathlib
import Definitions.Def_BadLocalMin_Smooth_Model

namespace BadLocalMin.Smooth

/-- §6.3, eqs. (43)–(50), pp. 23–24. For Θ satisfying (19a)–(19e), d_H ≥ 2, Y = σ(a)·1 − ΔY
with ΔY ≠ 0, and some Θ′ whose first neuron of the last hidden layer has positive inner
product with every row of ΔY (eq. (44), j = 1), E(Θ) = ‖ΔY‖²_F > 0 (eq. (43)) and some Θ*
has E(Θ*) < E(Θ) (eq. (50)). -/
theorem suboptimal_eq_43_50 (H N : ℕ) (d : ℕ → ℕ) (σ : ℝ → ℝ) (X : Fin (d 0) → Fin N → ℝ)
    (a : ℝ) (hH : 1 ≤ H) (hdH : 2 ≤ d H) (dY : Fin (d (H + 1)) → Fin N → ℝ) (hdY : dY ≠ 0)
    (θ : Params d H) (h19ad : Constr19ad σ a θ) (h19e : Constr19e θ)
    (h44 : ∃ θ' : Params d H, ∀ i : Fin (d (H + 1)),
      0 < ∑ n, dY i n * post σ X θ' H le_rfl ⟨0, by omega⟩ n) :
    0 < loss σ X (fun i n => σ a - dY i n) θ ∧
      ∃ θstar : Params d H,
        loss σ X (fun i n => σ a - dY i n) θstar < loss σ X (fun i n => σ a - dY i n) θ := by sorry

end BadLocalMin.Smooth
