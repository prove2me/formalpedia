-- Prove2me | Theorems.Thm_ExploreLQMFG_lemma_2_8
-- name    : ExploreLQMFG.lemma_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:13:49.681701+00:00
-- url     : https://prove2.me/theorems/34f1e12a-5169-44f2-b946-f02ab784ef26
-- title:
--   Lemma 2.8, p.23 — $|\nabla_x\theta_\varepsilon(t,x)|\le C_1/\varepsilon^2$
-- statement:
--   Fix $d\ge1$, $T>0$ and bounds $L_f,L_g$. There is a constant $C_1$ such that for all $d\times d$ matrices $Q,R$, all bounded Lipschitz $f,g$ with $\|Q^\dagger f\|_{1,\infty}\le L_f$ and $\|R^\dagger g\|_{1,\infty}\le L_g$, every $\varepsilon\in(0,1]$, the Riccati solution $\eta$ of (2.3) and every classical solution $\theta_\varepsilon$ of the master equation (1.8),
--   $$|\nabla_x\theta_\varepsilon(t,x)|\le\frac{C_1}{\varepsilon^2},\qquad t\in[0,T),\ x\in\mathbb R^d.$$
--
--   This is the source of the factor $\exp(C/\varepsilon^2)$ in Theorem 2.4: through (2.18) it bounds the martingale integrand $k$ of the limit system, and hence the drift change between the tilted measures.
--
--   Differences from the source:
--   - encoding: a constant depending only on d, T, ‖Q†f‖_{1,∞} and ‖R†g‖_{1,∞} → for every d ≥ 1, T > 0 and bounds L_f, L_g there is a constant valid for all Q, R, f, g with ‖Q†f‖_{1,∞} ≤ L_f and ‖R†g‖_{1,∞} ≤ L_g, all ε, ϖ and all data; reason: the uniform form of 'depends only on'; it is at least as strong as a function of the exact norms
--   - encoding: ℝᵈ with the Euclidean norm |·|; |·| on d × d matrices unnamed → Fin d → ℝ with |x|² = Σᵢ xᵢ² written explicitly; matrices carry the Frobenius norm; reason: Mathlib's default norm on Fin d → ℝ is the sup norm; all matrix norms are equivalent up to a factor depending only on d, which the constants absorb
--   - encoding: θ_ε, 'the solution of the PDE (1.8)' → every classical solution θ in the class IsClassicalSol; reason: the solution is unique in that class (milestone (1.8))
-- source:
--   Delarue & Vasileiadis, Exploration Noise for Learning Linear-Quadratic Mean Field Games, arXiv:2107.00839v2 (https://arxiv.org/abs/2107.00839v2), Lemma 2.8, p.23

import Mathlib
import Definitions.Def_ExploreLQMFG_Master

open MeasureTheory Filter
open scoped NNReal Matrix

namespace ExploreLQMFG

/-- **Lemma 2.8** (Delarue & Vasileiadis, arXiv:2107.00839v2, p.23): there exists a constant
`C₁`, only depending on `d`, `T`, `‖Q†f‖_{1,∞}` and `‖R†g‖_{1,∞}`, such that
`|∇ₓθ_ε(t, x)| ≤ C₁/ε²` for `t ∈ [0, T)`, `x ∈ ℝᵈ`, with `θ_ε` the solution of the PDE (1.8).

**Formalization Note.**
1. "Only depending on `d, T` and the norms" is encoded as: for every `d ≥ 1`, `T > 0` and
   bounds `L_f, L_g` there is `C₁` that works for all `Q, R, f, g` with
   `‖Q†f‖_{1,∞} ≤ L_f`, `‖R†g‖_{1,∞} ≤ L_g` and every `ε ∈ (0, 1]` (§2.1, p.19).
2. "The solution" is any classical solution in the class `IsClassicalSol` (it is unique);
   `|·|` on the Jacobian is the Frobenius norm. -/
theorem lemma_2_8 {d : ℕ} (hd : 0 < d) (T : ℝ≥0) (hT : 0 < T) (Lf Lg : ℝ) :
    ∃ C₁ : ℝ, ∀ (Q R : Matrix (Fin d) (Fin d) ℝ) (f g : (Fin d → ℝ) → (Fin d → ℝ)),
      IsBddLip f → IsBddLip g → oneInfNorm (tmul Q f) ≤ Lf → oneInfNorm (tmul R g) ≤ Lg →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ η : ℝ → Matrix (Fin d) (Fin d) ℝ, IsRiccatiSol Q R T η →
      ∀ θ, IsClassicalSol T ε η (tmul Q f) (tmul R g) θ →
      ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, frob (gradMat θ t x) ≤ C₁ / ε ^ 2 := by sorry

end ExploreLQMFG
