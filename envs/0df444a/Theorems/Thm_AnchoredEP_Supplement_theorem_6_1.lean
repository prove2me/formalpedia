-- Prove2me | Theorems.Thm_AnchoredEP_Supplement_theorem_6_1
-- name    : AnchoredEP.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:15:21.108754+00:00
-- url     : https://prove2.me/theorems/e508495a-b750-48a9-92c2-c4b00697a0de
-- title:
--   Theorem 6.1 — lower bound $\|F(z_N)\|\ge C_pL_pR^p/(N+1)^{(3p-1)/2}$ for deterministic $p$th-order methods
-- statement:
--   Fix an integer $p\ge2$. There is a constant $C_p>0$, depending only on $p$, such that the following holds. Let $L_p>0$, $R>0$, and let $N,n$ be positive integers with $n\ge2N+1$. Fix a starting point $z_0\in\mathbb R^n$. For every deterministic $p$th-order method initialized at $z_0$ there exists an operator $F:\mathbb R^n\to\mathbb R^n$ such that
--
--   1. $F$ is $(p-1)$ times continuously differentiable and $D^{p-1}F$ is $L_p$-Lipschitz;
--   2. $F$ is monotone: $\langle F(x)-F(y),x-y\rangle\ge0$ for all $x,y$;
--   3. $F$ has a unique zero $z^\ast$, and $\|z_0-z^\ast\|\le R$;
--   4. the output $z_N$ of the method after $N$ oracle queries satisfies
--   $$
--   \mathrm{res}^{\tan}(z_N)=\|F(z_N)\|\ \ge\ C_p\,\frac{L_pR^p}{(N+1)^{(3p-1)/2}} .
--   $$
--
--   Here $H=0$, so the tangent residual is $\|F\|$. The bound shows that the exponent $2/(3p-1)$ in the oracle complexity of the AEP Tensor Method (Theorem 5.1) cannot be improved by any deterministic $p$th-order method.
--
--   Differences from the source:
--   - encoding: a deterministic pth-order method: z_t an arbitrary deterministic function of z₀ and {D^jF(z_s) : 0 ≤ j ≤ p−1, 0 ≤ s < t}; the output after N oracle queries → M : PthOrderMethod p n (arbitrary maps from Fin t → OracleOutput p n to ℝ^n), chosen after z₀; output methodIterate M z0 F N, with oracle outputs iteratedFDeriv ℝ j F at the previous points; reason: the method is any function of the past oracle outputs, as in the source; dependence on z₀ is carried by M since z₀ is fixed first; the operator is chosen after the method
--   - encoding: a constant C_p > 0 depending only on p → ∃ C > 0 quantified after p and before L_p, R, N, n, the starting point and the method; reason: the source's quantifier order
--   - encoding: positive integers N, n with n ≥ 2N + 1 → N n : ℕ with 0 < N and 2 * N + 1 ≤ n; reason: n ≥ 2N + 1 ≥ 3 makes n positive
--   - encoding: (p−1)-times continuously differentiable with L_p-Lipschitz D^{p−1} → Assumption51 p L F (ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv ℝ (p−1) F z − iteratedFDeriv ℝ (p−1) F z′‖ ≤ L‖z − z′‖); reason: the same two conditions; the operator norm of iteratedFDeriv is the induced multilinear norm
--   - encoding: monotone operator F → IsMonotoneOp (fun x => {F x}) (the published monotone-operator predicate on the single-valued operator); reason: for a single-valued operator this is ⟨x − y, F x − F y⟩ ≥ 0 for all x, y
--   - encoding: a unique zero z∗ satisfying ‖z₀ − z∗‖ ≤ R → ∃ zstar, F zstar = 0 ∧ (∀ y, F y = 0 → y = zstar) ∧ ‖z0 − zstar‖ ≤ R; reason: existence and uniqueness written out
--   - encoding: res^tan(z_N) = ‖F(z_N)‖ ≥ C_p L_p R^p/(N + 1)^{(3p−1)/2}, with H = 0 → C * L * R ^ p / ((N : ℝ) + 1) ^ ((3p − 1)/2) ≤ ‖F (methodIterate M z0 F N)‖; reason: with H = 0 the tangent residual is ‖F(z)‖, the source's own equality in (28); the exponent is a real power
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Theorem 6.1, p.12

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_Supplement_PthOrderMethod
import Definitions.Def_AnchoredEP_Supplement_methodIterate

open ThreeOpSplitting.Convergence

namespace AnchoredEP.Supplement

/-- **Theorem 6.1 (lower bound for `p`th-order methods on monotone equations).** Jiang–Yoon,
arXiv:2609.30212, Theorem 6.1, p.12: "Fix an integer `p ≥ 2`. There is a constant `C_p > 0`,
depending only on `p`, such that the following holds. Let `L_p > 0`, `R > 0`, and let `N, n` be
positive integers such that `n ≥ 2N + 1`. Fix a starting point `z₀ ∈ ℝ^n`. For every deterministic
`p`th-order method initialized at `z₀`, there exists a `(p − 1)`-times continuously differentiable
and monotone operator `F : ℝ^n → ℝ^n` with a unique zero `z∗` satisfying `‖z₀ − z∗‖ ≤ R` such that
`D^{p−1}F` is `L_p`-Lipschitz, for which the output of the algorithm after `N` oracle queries
satisfies `res^tan(z_N) = ‖F(z_N)‖ ≥ C_p L_p R^p/(N + 1)^{(3p−1)/2}`. (28)"

**Formalization Note.** A deterministic `p`th-order method is any `M : PthOrderMethod p n`; it is
chosen after `z₀` and before `F`, and sees `F` only through the oracle outputs
`D^jF(z_s)`, `0 ≤ j ≤ p − 1`, at its previous points (`methodIterate`). The output after `N` queries
is `z_N = methodIterate M z0 F N`. "`(p−1)`-times continuously differentiable with
`L_p`-Lipschitz `D^{p−1}F`" is the published `Assumption51 p L F`
(`ContDiff ℝ (p−1) F ∧` the Lipschitz bound on `iteratedFDeriv ℝ (p−1) F`). Monotonicity is the
published `IsMonotoneOp` applied to the single-valued operator `x ↦ {F x}`. Since `H = 0`,
`res^tan(z) = ‖F(z)‖`, and the bound is stated on `‖F(z_N)‖`. `(N + 1)^{(3p−1)/2}` is `Real.rpow`. -/
theorem theorem_6_1 (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L R : ℝ) (N n : ℕ), 0 < L → 0 < R → 0 < N → 2 * N + 1 ≤ n →
      ∀ (z0 : EuclideanSpace ℝ (Fin n)) (M : PthOrderMethod p n),
      ∃ F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Assumption51 p L F ∧
        IsMonotoneOp (fun x => ({F x} : Set (EuclideanSpace ℝ (Fin n)))) ∧
        (∃ zstar : EuclideanSpace ℝ (Fin n), F zstar = 0 ∧ (∀ y : EuclideanSpace ℝ (Fin n), F y = 0 → y = zstar) ∧
          ‖z0 - zstar‖ ≤ R) ∧
        C * L * R ^ p / ((N : ℝ) + 1) ^ ((3 * (p : ℝ) - 1) / 2) ≤
          ‖F (methodIterate M z0 F N)‖ := by sorry

end AnchoredEP.Supplement
