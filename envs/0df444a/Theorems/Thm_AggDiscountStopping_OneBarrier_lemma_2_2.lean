-- Prove2me | Theorems.Thm_AggDiscountStopping_OneBarrier_lemma_2_2
-- name    : AggDiscountStopping.OneBarrier.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:00.064987+00:00
-- url     : https://prove2.me/theorems/dc545c4e-dafe-4e75-b79c-fab3de7af72e
-- title:
--   Lemma 2.2, p. 7, for the regions R = [0, a] — τ(x, [0, a]) = 0 a.s. and ϕ(g(x)) = J(x, [0, a]) for 0 ≤ x ≤ a
-- statement:
--   Consider the aggregated stopping model with its standing assumptions, a diffusion with continuous non-negative paths, and a Laplace representation $\mathbb E[e^{-r\tau^x_a}]=\varphi_r(x)/\varphi_r(a)$ as in Remark 4.3. Let $a>0$ and $0\le x\le a$. Then almost surely the path started at $x$ enters $[0,a]$ immediately,
--   $$\tau(x,[0,a])=\inf\{t>0: X^x_t\in[0,a]\}=0,$$
--   and consequently
--   $$\phi(g(x))=J(x,[0,a]).$$
--
--   This is the instance of Lemma 2.2 used in the proof of Theorem 4.8: a point of a one-barrier region is indifferent between stopping and continuing, so the region is contained in its own image under $\Theta$.
--
--   **Formalization Note** The paper states the lemma for every Borel $R$ and every $x$ in its closure; it is posed here only for $R=[0,a]$, $a>0$, which is the case Theorem 4.8 uses. The general case needs regularity of every boundary point from both sides, which the encoding does not carry. At the boundary point $x=a$ the instantaneous return is supplied by the Laplace representation at $x=a$ ($\mathbb E[e^{-\tau^a_a}]=1$), which every regular diffusion satisfies.
-- source:
--   Deng, Yu, Zhang, On time-consistent equilibrium stopping under aggregation of diverse discount rates, arXiv:2302.07470v4, Lemma 2.2, p. 7 (for R = [0, a])

import Mathlib
import Definitions.Def_AggDiscountStopping_OneBarrier_Setting

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace AggDiscountStopping.OneBarrier

theorem lemma_2_2 {Ω : Type*} [MeasurableSpace Ω] (M : Model) (hM : M.Valid)
    (D : Diffusion Ω) (hD : D.Valid) (φ : ℝ → ℝ → ℝ) (hφ : IsLaplaceRep M D φ)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∀ᵐ ω ∂D.P, D.enters x (Icc 0 a) ω ∧ D.entryTime x (Icc 0 a) ω = 0) ∧
      J M D x (Icc 0 a) = M.att (M.g x) := by sorry

end AggDiscountStopping.OneBarrier
