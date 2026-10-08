-- Prove2me | Theorems.Thm_BanditGD_Regret_theorem_1
-- name    : BanditGD.Regret.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:28:47.196281+00:00
-- url     : https://prove2.me/theorems/05779ab3-f195-4aa1-9d67-2660a204b5d9
-- title:
--   Theorem 1, p. 8 — BGD with ν = R/(C√n), δ = ∛(rR²d²/12n), α = ∛(3Rd/2r√n) has expected regret ≤ 3Cn^{5/6}∛(12dR/r) (constant as derived on p. 9)
-- statement:
--   **Model** (§1.2 and §1.4). Let $d\ge1$ and let $S\subseteq\mathbb R^d$ be a closed convex feasible set with
--   $$r\mathbb B\subseteq S\subseteq R\mathbb B$$
--   for some $r>0$, where $\mathbb B$ is the closed unit ball. Let $C>0$ and let $c_1,c_2,\dots$ be a sequence of cost functions fixed in advance (an oblivious adversary), each convex on $S$ with $c_t(x)\in[-C,C]$ for $x\in S$. The decision maker observes only the value $c_t(x_t)$ at the point $x_t$ it plays.
--
--   **Algorithm** (Figure 1). $\mathrm{BGD}(\alpha,\delta,\nu)$ starts at $y_1=0$; at each period $t$ it draws a unit vector $u_t$ uniformly at random, independently of the past, plays $x_t=y_t+\delta u_t$, and sets $y_{t+1}=P_{(1-\alpha)S}\big(y_t-\nu c_t(x_t)u_t\big)$, where $P_{(1-\alpha)S}$ is the nearest-point projection onto $(1-\alpha)S$.
--
--   **Theorem.** For every $n\ge(3Rd/2r)^2$ and
--   $$\nu=\frac{R}{C\sqrt n},\qquad\delta=\sqrt[3]{\frac{rR^2d^2}{12n}},\qquad\alpha=\sqrt[3]{\frac{3Rd}{2r\sqrt n}},$$
--   the expected regret of $\mathrm{BGD}(\alpha,\delta,\nu)$ satisfies
--   $$\mathbb E\Big[\sum_{t=1}^n c_t(x_t)\Big]-\min_{x\in S}\sum_{t=1}^n c_t(x)\le 3Cn^{5/6}\sqrt[3]{\frac{12dR}{r}} .$$
--
--   This is the main result of the paper: gradient descent run on one function value per round has regret $O(n^{5/6})$ against any fixed sequence of bounded convex costs, with no Lipschitz or differentiability assumption.
--
--   **Formalization Note** The printed constant $3Cn^{5/6}\sqrt[3]{dR/r}$ omits the factor $\sqrt[3]{12}$ that the paper's own final step produces: the proof bounds the regret by $a/\delta+b\delta/\alpha+c\alpha$ with $a=RdC\sqrt n$, $b=6Cn/r$, $c=2Cn$, and the stated $\delta,\alpha$ give the value $3\sqrt[3]{abc}=3Cn^{5/6}\sqrt[3]{12dR/r}$. This item states the bound the proof establishes. Added or read conventions: $S$ is closed (the projection oracle of §1.4 presupposes that the minimum distance is attained); the directions $u_1,u_2,\dots$ are measurable, independent and each uniform on the unit sphere; $d\ge1$; rounds are numbered from $1$; the minimum is an infimum over $S$; the costs are functions on $\mathbb R^d$ and nothing is assumed about them outside $S$. The run is required for every outcome of the probability space; the theorem prints "BGD(ν, δ, α)", the same algorithm as Figure 1's $\mathrm{BGD}(\alpha,\delta,\nu)$.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 8, Theorem 1 (constant as derived on p. 9)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
open MeasureTheory
open scoped Pointwise

namespace BanditGD.Regret

theorem theorem_1 {d : ℕ} (hd : 1 ≤ d)
    (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S) (hSclosed : IsClosed S)
    (r R : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (hSR : S ⊆ Metric.closedBall 0 R)
    (C : ℝ) (hC : 0 < C) (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcconv : ∀ t, ConvexOn ℝ S (c t)) (hcbdd : ∀ t, ∀ x ∈ S, |c t x| ≤ C)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hum : ∀ t, Measurable (u t))
    (hind : ProbabilityTheory.iIndepFun u P)
    (hlaw : ∀ t, P.map (u t) = RegretBandits.Nonlinear.uniformSphere d)
    (y : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (hn : (3 * R * d / (2 * r)) ^ 2 ≤ (n : ℝ))
    (ν δ α : ℝ) (hν : ν = R / (C * Real.sqrt n))
    (hδ : δ = (r * R ^ 2 * d ^ 2 / (12 * n)) ^ ((1 : ℝ) / 3))
    (hα : α = (3 * R * d / (2 * r * Real.sqrt n)) ^ ((1 : ℝ) / 3))
    (hrun : ∀ ω, IsBGDRun S α δ ν c (fun t => u t ω) (fun t => y t ω)) :
    RegretBandits.Nonlinear.pseudoRegret S c P (fun t ω => y t ω + δ • u t ω) n
      ≤ 3 * C * (n : ℝ) ^ ((5 : ℝ) / 6) * (12 * d * R / r) ^ ((1 : ℝ) / 3) := by sorry

end BanditGD.Regret
