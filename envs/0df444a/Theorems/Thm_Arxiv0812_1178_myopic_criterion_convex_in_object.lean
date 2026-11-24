-- Prove2me | Theorems.Thm_Arxiv0812_1178_myopic_criterion_convex_in_object
-- name    : Arxiv0812_1178.myopic_criterion_convex_in_object
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T08:52:32.76519+00:00
-- url     : https://prove2.me/theorems/c62b6e8b-4f42-4ccb-89c0-200a6e25a433
-- title:
--   Sec. 3.C, eq. (35), and Sec. 4.B: $J^{data}(x,\alpha)$ is quadratic, hence convex, in $x$
-- statement:
--   Let $N_t\ge3$ and fix finitely many measurement instants $t$. For each $t$ fix the pseudo complex visibilities $y^{data}(t)$, the noise mean $\bar y^{noise}(t)$ and a positive definite noise covariance $R_{y^{noise}(t)}$, none of which depend on the object $x$. Fix the aberrations $\alpha=(\alpha(t))_t$. Then the myopic criterion
--   $$J^{data}(x,\alpha)=\sum_t\chi^2_{y(t)}(x,\alpha(t))$$
--   is a quadratic function of $x\in\mathbb R^P$: it equals $x^{\mathsf T}Qx+q^{\mathsf T}x+c$ for some $Q,q,c$. It is convex in $x$. For every convex regularization term $J^{prior}$, the regularized criterion $x\mapsto J^{data}(x,\alpha)+J^{prior}(x)$ (eq. (36)) is convex.
--
--   **Formalization Note** The paper never says where $\bar y^{noise}(t)$ and $R_{y^{noise}(t)}$ are evaluated. Appendix E writes them in terms of the noise-free modulus and phase, which depend on $x$. Here they are fixed parameters independent of $x$, which is the reading the convexity claim needs. Convexity is stated on all of $\mathbb R^P$, which contains the convex constraint set (16).
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), claim c017; Sec. 2.E, first bullet after item (iii), PDF p. 7; Sec. 3.C, eqs. (34)-(36), PDF p. 10; Sec. 4.B, paragraph 'Minimization w.r.t. x', PDF p. 12

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv0812_1178

theorem myopic_criterion_convex_in_object {n : ℕ} (hn : 3 ≤ n) {T P : Type*} [Fintype T]
    [Fintype P] (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (hR : ∀ t, (R t).PosDef) (α : T → Fin (n - 1) → ℝ) :
    (∃ (Q : Matrix P P ℝ) (q : P → ℝ) (c : ℝ), ∀ x : P → ℝ,
      myopicCrit H ydata ybar R x α = x ⬝ᵥ (Q *ᵥ x) + q ⬝ᵥ x + c) ∧
    ConvexOn ℝ Set.univ (fun x => myopicCrit H ydata ybar R x α) ∧
    ∀ Jprior : (P → ℝ) → ℝ, ConvexOn ℝ Set.univ Jprior →
      ConvexOn ℝ Set.univ (fun x => myopicCrit H ydata ybar R x α + Jprior x) := by sorry

end Arxiv0812_1178
