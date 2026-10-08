-- Prove2me | Theorems.Thm_DaiWeissFluid_ThreeBuffer_lemma3_2
-- name    : DaiWeissFluid.ThreeBuffer.lemma3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:28:14.039671+00:00
-- url     : https://prove2.me/theorems/5aa0cad4-60f3-4165-a0ca-24db3aa2e506
-- title:
--   Lemma 3.2 — the maximum of linear Lyapunov components has drift ≤ −min εᵢ
-- statement:
--   Consider a reentrant line with $I \ge 1$ stations and $K$ classes, mean service times $m_k > 0$, and a fluid model solution $(Q, T)$ satisfying (1.8)–(1.12). For each station $i$ let $G_i(t) = \sum_{k} c_{ik} Q_k(t)$ be a linear function of the fluid levels with nonnegative coefficients $c_{ik} \ge 0$, and let $W_i(t) = \sum_{k \in C_i} m_k Q_k(t)$ be the immediate volume of station $i$. Assume:
--
--   1. (a) for each $i$ there is $\varepsilon_i > 0$ such that, at every $t > 0$ with $W_i(t) > 0$ at which $G_i$ is differentiable, $\dot G_i(t) \le -\varepsilon_i$;
--   2. (b) for each $i$ and each $t \ge 0$, if $W_i(t) = 0$ then $G_i(t) \le G_j(t)$ for every $j \ne i$.
--
--   Let $G(t) = \max\{G_1(t), \dots, G_I(t)\}$. Then $G$ is absolutely continuous on every compact interval of $[0,\infty)$ and nonnegative there, and at every $t > 0$ at which $G, G_1, \dots, G_I$ are all differentiable and $G(t) > 0$,
--
--   $$
--   \dot G(t) \le -\varepsilon, \qquad \varepsilon = \min\{\varepsilon_1, \dots, \varepsilon_I\}.
--   $$
--
--   The lemma turns station-wise drift conditions into a single drift bound for a piecewise-linear Lyapunov function; combined with Lemma 2.2 it yields stability of a fluid model.
--
--   **Formalization Note.** Stations and classes are 0-based. "Nonnegative linear function of $Q(t)$" is encoded by time-independent nonnegative coefficients `c i k`. The maximum is `⨆ i : Fin I`, a supremum over a finite nonempty index type (the hypothesis $0 < I$ makes it a genuine maximum and makes the minimum of the $\varepsilon_i$ well defined, written `Finset.univ.inf' _ ε`). The lemma assumes only (1.8)–(1.12) and $m_k > 0$, not work conservation, as in the paper. A "regular point" is a time $t>0$ at which the relevant functions are differentiable (`HasDerivAt`, `DifferentiableAt`).
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), pp. 121–122, Lemma 3.2

import Mathlib
import Definitions.Def_DaiWeissFluid_ThreeBuffer_FluidModel

namespace DaiWeissFluid.ThreeBuffer

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

end DaiWeissFluid.ThreeBuffer
