-- Prove2me | Theorems.Thm_AddictivePlatforms_Costly_lemma_D_1
-- name    : AddictivePlatforms.Costly.lemma_D_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:38:34.648807+00:00
-- url     : https://prove2.me/theorems/91605f1d-5eac-46ac-a0ba-538bb5291b2a
-- title:
--   Lemma D.1, pp. 33–34 — the consumer's optimal attention on all K platforms is (1/K)[min{A(D), Ā} − D] + d_k (under interiority); A(·) concave
-- statement:
--   Work under Assumptions 1–3 with $u(a,d) = v(a-d)$, $K \ge 1$ platforms and a cap $\overline{A} \in \mathbb{R}_+\cup\{\infty\}$, and let $g = (v')^{-1}$.
--
--   1. There is a function $A : \mathbb{R}_+ \to \mathbb{R}_+$ such that for every $D \ge 0$
--   $$A(D) - D = K\, g\big(C'(A(D))\big),$$
--   and $A(D)$ is the only solution of this equation in $\mathbb{R}_+$.
--   2. $A$ is concave on $\mathbb{R}_+$.
--   3. Suppose the consumer joins all $K$ platforms with addictiveness $(d_1,\dots,d_K) \ge 0$, and let $D = \sum_k d_k$. If every coordinate of
--   $$a_k = \frac{1}{K}\Big[\min\{A(D), \overline{A}\} - D\Big] + d_k \qquad \text{(A.6)}$$
--   is nonnegative, then (A.6) is the unique attention profile maximizing $\sum_k v(a_k - d_k) - C(\sum_k a_k)$ subject to $a_k \ge 0$ and $\sum_k a_k \le \overline{A}$.
--
--   The lemma reduces the consumer's allocation to one scalar, the total attention $\min\{A(D),\overline{A}\}$, which depends on the addictiveness profile only through its sum. This reduction underlies the platform payoff (A.10) and the analysis of the equilibrium and of the joint-profit maximizing outcome.
--
--   **Formalization Note.** The page states (A.6) for every profile; it can fail without the hypothesis that its right-hand side is nonnegative (for $v(x) = 1 - e^{-x}$, $C(a) = (e^a-1)/2$, $K = 2$, $\overline{A} = \infty$, $d = (0,5)$ it gives $a_1 \approx -1.44$), because the proof's first-order condition ignores $a_k \ge 0$. The interiority hypothesis is therefore added. Standing pins: strict concavity of $u(\cdot,d)$, $C(0) = 0$, existence of the uncapped optimum, and the reading of $g = (v')^{-1}$ described in the model file.
-- source:
--   Ichihashi & Kim, Addictive Platforms, Bank of Canada SWP 2022-16 (Apr. 1, 2022), pp. 33–34, Lemma D.1, (A.6), and its proof ((A.7), (A.8))

import Mathlib
import Definitions.Def_AddictivePlatforms_Costly_Model

open Set Filter Topology
open scoped ENNReal

namespace AddictivePlatforms.Costly

/-- Lemma D.1 (pp. 33–34). Under the standing hypotheses of §5 with `K ≥ 1` platforms there is a
function `A : ℝ₊ → ℝ₊` such that `A(D)` solves `A(D) − D = K g(C′(A(D)))` for every `D ≥ 0`; the
solution in `ℝ₊` is unique; `A` is concave on `ℝ₊`; and for every profile `d ≥ 0` for which the
right-hand side of (A.6) is nonnegative for every `k` (the disclosed interiority hypothesis), the
consumer who has joined all `K` platforms has a unique optimal attention profile, given by (A.6):
`a_k = (1/K) [min{A(D), Ā} − D] + d_k` with `D = ∑_k d_k`. -/
theorem lemma_D_1 (v C γ g : ℝ → ℝ) (K : ℕ) (hK : 0 < K) (hS : Standing v C γ g K)
    (Abar : ℝ≥0∞) :
    ∃ AD : ℝ → ℝ, IsAD C g K AD ∧
      (∀ D : ℝ, 0 ≤ D → ∀ A : ℝ, 0 ≤ A → A - D = (K : ℝ) * g (AddictivePlatforms.Compete.Cderiv C A) → A = AD D) ∧
      ConcaveOn ℝ (Ici 0) AD ∧
      ∀ d : Fin K → ℝ, (∀ k, 0 ≤ d k) → (∀ k, 0 ≤ allocA6 AD Abar d k) →
        ∀ a : Fin K → ℝ, IsAllocOpt (uOf v) C Abar d a ↔ a = allocA6 AD Abar d := by sorry

end AddictivePlatforms.Costly
