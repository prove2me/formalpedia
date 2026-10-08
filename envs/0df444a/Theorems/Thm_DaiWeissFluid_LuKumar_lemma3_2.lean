-- Prove2me | Theorems.Thm_DaiWeissFluid_LuKumar_lemma3_2
-- name    : DaiWeissFluid.LuKumar.lemma3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:05:37.37309+00:00
-- url     : https://prove2.me/theorems/419e60e9-8e38-41ae-b628-57621c3677c4
-- title:
--   Lemma 3.2 — negative drift of a maximum of linear components
-- statement:
--   Let a reentrant line have a positive number $I$ of stations and positive service times. For a fluid solution, let $G_i(t)=\sum_k c_{ik}Q_k(t)$ with $c_{ik}\ge0$, and let $\varepsilon_i>0$. Assume: (a) whenever the immediate workload $W_i(t)>0$ at a positive regular time, the derivative of $G_i$ is at most $-\varepsilon_i$; and (b) whenever $W_i(t)=0$, $G_i(t)\le G_j(t)$ for every $j\ne i$. Set $G(t)=\max_iG_i(t)$. Then $G$ is absolutely continuous and nonnegative on nonnegative time, and at every positive time where $G$ and all components are differentiable,
--   $$G(t)>0\quad\Longrightarrow\quad\dot G(t)\le-\min_i\varepsilon_i.$$
--   This is the finite-component Lyapunov principle used to prove the stable half of the Lu–Kumar result.
--
--   **Formalization Note** The maximum and minimum run over the nonempty finite station set. Conditions (a) and (b) are hypotheses, while the fluid equations imply the required regularity; work conservation is not assumed. Linear nonnegativity is encoded by nonnegative coefficients. Indices are zero-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 121, Lemma 3.2

import Mathlib
import Definitions.Def_DaiWeissFluid_LuKumar_FluidModel
import Definitions.Def_DaiWeissFluid_LuKumar_Network

namespace DaiWeissFluid.LuKumar

/-- Lemma 3.2: the maximum of finitely many linear Lyapunov components has negative drift. -/
theorem lemma3_2 {I K : ℕ} (L : ReentrantLine I K)
    (hm : ∀ k, 0 < L.m k) (hI : 0 < I)
    (Q T : ℝ → Fin K → ℝ) (hsol : L.IsFluidSolution Q T)
    (c : Fin I → Fin K → ℝ) (hc : ∀ i k, 0 ≤ c i k)
    (ε : Fin I → ℝ) (hε : ∀ i, 0 < ε i)
    (ha : ∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, c i k * Q s k) d t → d ≤ -ε i)
    (hb : ∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, c i k * Q t k ≤ ∑ k, c j k * Q t k) :
    let G : ℝ → ℝ := fun s => ⨆ i : Fin I, ∑ k, c i k * Q s k
    (∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval G a b) ∧
    (∀ t, 0 ≤ t → 0 ≤ G t) ∧
    (∀ t d, 0 < t → 0 < G t → HasDerivAt G d t →
      (∀ i, DifferentiableAt ℝ (fun s => ∑ k, c i k * Q s k) t) →
      d ≤ -(⨅ i : Fin I, ε i)) := by sorry

end DaiWeissFluid.LuKumar
