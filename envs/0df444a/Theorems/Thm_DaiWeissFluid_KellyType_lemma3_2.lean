-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_lemma3_2
-- name    : DaiWeissFluid.KellyType.lemma3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:46:11.458349+00:00
-- url     : https://prove2.me/theorems/f802c2d2-293f-49c2-862d-2ceae1d4ddec
-- title:
--   Lemma 3.2 — the maximum of linear Lyapunov components has drift ≤ −min εᵢ
-- statement:
--   Consider a reentrant line with $I \ge 1$ stations, positive mean service times $m_k$, and a fluid model solution $(Q,T)$ of (1.8)–(1.12). Let
--
--   $$ G_i(t) = \sum_{k=1}^K c_{i,k}\,Q_k(t), \qquad c_{i,k} \ge 0,\quad i = 1,\dots,I, $$
--
--   be nonnegative linear functions of the queue lengths and $G(t) = \max\{G_1(t),\dots,G_I(t)\}$. Assume
--
--   (a) for each $i$ there is $\varepsilon_i > 0$ such that $W_i(t) > 0$ implies $\dot G_i(t) \le -\varepsilon_i$;
--
--   (b) for each $i$, if $W_i(t) = 0$ then $G_i(t) \le \min_{j \ne i} G_j(t)$.
--
--   Then $G$ is absolutely continuous and nonnegative on $[0,\infty)$, and if $t > 0$ is a regular point of $G, G_1, \dots, G_I$ with $G(t) > 0$, then
--
--   $$ \dot G(t) \le -\varepsilon, \qquad \varepsilon = \min\{\varepsilon_1,\dots,\varepsilon_I\}. $$
--
--   This lemma builds a piecewise-linear Lyapunov function from per-station drift estimates; it feeds Lemma 2.2 in Theorems 3.1, 5.1 and 6.1.
--
--   **Formalization Note** "Nonnegative linear function" is encoded by nonnegative coefficients $c_{i,k}$. Condition (a) is required at $t > 0$ for every derivative of $G_i$ at $t$ (`HasDerivAt`); condition (b) at $t \ge 0$. The lemma is stated for any reentrant line and assumes only (1.8)–(1.12) and $m_k > 0$, not work conservation, as in the paper. The maximum is `⨆ i` over the finite type `Fin I`; $I \ge 1$ is assumed so that it and $\min_i \varepsilon_i$ are meaningful.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, Lemma 3.2

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel

namespace DaiWeissFluid.KellyType

/-- Lemma 3.2, p. 121, for an arbitrary reentrant line with `I ≥ 1` stations: let
`G_i(t) = ∑_k c i k * Q_k(t)` with nonnegative coefficients and `G(t) = max_i G_i(t)`. If
(a) `W_i(t) > 0` implies `Ġ_i(t) ≤ -ε_i`, and (b) `W_i(t) = 0` implies `G_i(t) ≤ G_j(t)` for all
`j ≠ i`, then `G` is absolutely continuous and nonnegative on `[0, ∞)`, and at every regular point
`t > 0` of `G, G_1, …, G_I` with `G(t) > 0`, `Ġ(t) ≤ -min_i ε_i`. -/
theorem lemma3_2 {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k) (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    (∀ a b, 0 ≤ a → a ≤ b →
        AbsolutelyContinuousOnInterval (fun s => ⨆ i, ∑ k, c i k * Q s k) a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ ⨆ i, ∑ k, c i k * Q t k) ∧
    (∀ t, 0 < t → 0 < (⨆ i, ∑ k, c i k * Q t k) →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      ∀ d, HasDerivAt (fun s => ⨆ i, ∑ k, c i k * Q s k) d t →
        d ≤ -(Finset.univ.inf' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hI⟩⟩) ε)) := by sorry

end DaiWeissFluid.KellyType
