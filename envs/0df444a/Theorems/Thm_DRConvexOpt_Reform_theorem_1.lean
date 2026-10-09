-- Prove2me | Theorems.Thm_DRConvexOpt_Reform_theorem_1
-- name    : DRConvexOpt.Reform.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:47.007963+00:00
-- url     : https://prove2.me/theorems/bb07d693-ce24-4adc-8a82-93ccd3e1e8bb
-- title:
--   Theorem 1, pp. 10–11 — under (C1)–(C3), (N) and moment-problem regularity, the constraint (3) holds iff the conic system in (β, κ, λ, φ_il) is feasible
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set (4), with confidence sets (5) defined by proper cones $\mathcal K_i$ and probability bounds $0 \le \underline p_i \le \overline p_i \le 1$. Assume
--
--   1. (C1): $\mathcal C_I$ is bounded and $\underline p_I = \overline p_I = 1$;
--   2. (C2): some $\mathbb P \in \mathcal P$ has $\mathbb P[(\tilde z,\tilde u) \in \mathcal C_i] \in (\underline p_i, \overline p_i)$ whenever $\underline p_i < \overline p_i$;
--   3. (C3): $v(x,z) = \max_{l \in \mathcal L} \big[(S_l z + s_l)^\top x + \mathbf t_l^\top z + t_l\big]$;
--   4. (N): the nesting condition;
--   5. (S1) and (S2) of the Setting (regularity of the moment problem, and strict feasibility of each confidence set).
--
--   Then for every $x \in \mathbb R^N$ and $w \in \mathbb R$ the distributionally robust constraint
--   $$\mathbb E_{\mathbb P}[v(x,\tilde z)] \le w \qquad \forall \mathbb P \in \mathcal P \tag{3}$$
--   holds if and only if there are $\beta \in \mathbb R^K$, $\kappa, \lambda \in \mathbb R^I_+$ and $\phi_{il} \in \mathcal K_i^\star$, $i \in \mathcal I$, $l \in \mathcal L$, satisfying
--   $$\begin{aligned} & b^\top\beta + \sum_{i \in \mathcal I}\big[\overline p_i\kappa_i - \underline p_i \lambda_i\big] \le w,\\ & c_i^\top \phi_{il} + s_l^\top x + t_l \le \sum_{i' \in \mathcal A(i)}[\kappa_{i'} - \lambda_{i'}],\\ & C_i^\top\phi_{il} + A^\top \beta = S_l^\top x + \mathbf t_l,\\ & D_i^\top \phi_{il} + B^\top\beta = 0 \end{aligned} \qquad \forall i \in \mathcal I,\ \forall l \in \mathcal L.$$
--
--   When the confidence sets are described by linear, second-order cone or semidefinite inequalities, the system is a linear, conic-quadratic or semidefinite program, so the distributionally robust constraint is tractable under the nesting condition.
--
--   **Formalization Note** (S1) and (S2) are not in the paper. As printed, the "only if" direction is false: take $P = 2$, $Q = 0$, $K = I = L = 1$, $\mathcal C_1$ the unit disk, $\mathbb E[\tilde z_1] = 1$, $v(x,z) = z_2$ and $w = 0$; then $\mathcal P = \{\delta_{(1,0)}\}$, (C1)–(C3) and (N) hold and (3) holds, but the system forces $\phi_3 \ge \sqrt{\beta^2+1} > -\beta \ge \phi_3$. The proof's appeal to strong duality "due to condition (C2)" needs (S1), and Lemma 1's appeal to strict feasibility needs (S2). (S1) is a constraint qualification and costs some instances the page allows: it rules out $\overline p_i = 0$ and $\underline p_i = 1$ for $i \neq I$, and expectation rows that the measures on $\mathcal C_I$ cannot shift in every direction. The "if" direction needs neither (see the sufficiency milestone). The expectation $\mathbb E_{\mathbb P}[v(x,\tilde z)]$ is a genuine integral: members of $\mathcal P$ have a finite first moment and are concentrated on the bounded set $\mathcal C_I$, and $v$ is continuous. The scalar $t_l$ is `v.t0 l` and the vector $\mathbf t_l$ is `v.tv l`; indices are 0-based with $\mathcal C_I$ = `d.conf (Fin.last nI)`.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), pp. 10–11, Theorem 1 (Equivalent Reformulation)

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting

namespace DRConvexOpt.Reform

open MeasureTheory Matrix

/-- Theorem 1 (Equivalent Reformulation), pp. 10–11. Under (C1)–(C3) and (N), and the disclosed
additional assumptions (S1) `MomentSlater` and (S2) `ConfSlater`, the distributionally robust
constraint (3) holds for the ambiguity set (4) iff the conic system in `(β, κ, λ, φ_il)` is
feasible. The second system line uses the scalar `t_l` (`v.t0 l`), the third the vector `t_l`
(`v.tv l`). Indices are 0-based; `C_I` is `d.conf (Fin.last nI)`. -/
theorem theorem_1 {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hN : Nesting d) (hS1 : MomentSlater d) (hS2 : ConfSlater d)
    (x : Fin nN → ℝ) (w : ℝ) :
    (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ↔
    ∃ (β : Fin nK → ℝ) (κ lam : Fin (nI + 1) → ℝ)
      (φ : (i : Fin (nI + 1)) → Fin nL → Fin (d.L i) → ℝ),
      (∀ i, 0 ≤ κ i) ∧ (∀ i, 0 ≤ lam i) ∧ (∀ i l, φ i l ∈ dualCone (d.K i)) ∧
      d.b ⬝ᵥ β + ∑ i, (d.phi i * κ i - d.plo i * lam i) ≤ w ∧
      ∀ i l, d.c i ⬝ᵥ φ i l + v.s l ⬝ᵥ x + v.t0 l ≤ ∑ i' ∈ anc d i, (κ i' - lam i') ∧
        (d.C i)ᵀ *ᵥ φ i l + d.Aᵀ *ᵥ β = (v.S l)ᵀ *ᵥ x + v.tv l ∧
        (d.D i)ᵀ *ᵥ φ i l + d.Bᵀ *ᵥ β = 0 := by sorry

end DRConvexOpt.Reform
