-- Prove2me | Theorems.Thm_AnchoredEP_Supplement_theorem_6_4
-- name    : AnchoredEP.Supplement.theorem_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:16:02.887493+00:00
-- url     : https://prove2.me/theorems/45e89789-4436-40ce-9f55-acd815414991
-- title:
--   Theorem 6.4 — fixed-point lower bound $\|y_N-T(y_N)\|\ge\min\{R/(2(N+1)),C_pL_pR^p/(N+1)^{(3p-1)/2}\}$
-- statement:
--   Fix an integer $p\ge2$. There is a constant $C_p>0$, depending only on $p$, such that the following holds. Let $L_p>0$, $R>0$, and let $N,n$ be positive integers with $n\ge2N+1$. Fix a starting point $y_0\in\mathbb R^n$. For every deterministic $p$th-order method initialized at $y_0$ (with oracle outputs $D^jT$, $0\le j\le p-1$) there exists an operator $T:\mathbb R^n\to\mathbb R^n$ such that
--
--   1. $T$ is $(p-1)$ times continuously differentiable and $D^{p-1}T$ is $L_p$-Lipschitz;
--   2. $T$ is nonexpansive: $\|T(x)-T(y)\|\le\|x-y\|$ for all $x,y$;
--   3. $T$ has a fixed point $y^\ast$ with $\|y_0-y^\ast\|\le R$;
--   4. the output $y_N$ of the method after $N$ oracle queries satisfies
--   $$
--   \|y_N-T(y_N)\|\ \ge\ \min\Big\{\frac{R}{2(N+1)},\ C_p\,\frac{L_pR^p}{(N+1)^{(3p-1)/2}}\Big\}.
--   $$
--
--   When $N$ is small compared with $R^{2/3}$ the first term is active and matches the rate of first-order methods, so higher-order information does not help in that regime; when $N$ is large the second term is matched, up to a logarithmic factor, by the AEP Tensor Method applied to $F=I-T$.
--
--   Differences from the source:
--   - encoding: a deterministic pth-order method: z_t an arbitrary deterministic function of z₀ and {D^jF(z_s) : 0 ≤ j ≤ p−1, 0 ≤ s < t}; the output after N oracle queries → M : PthOrderMethod p n (arbitrary maps from Fin t → OracleOutput p n to ℝ^n), chosen after z₀; output methodIterate M z0 F N, with oracle outputs iteratedFDeriv ℝ j F at the previous points; reason: the method is any function of the past oracle outputs, as in the source; dependence on z₀ is carried by M since z₀ is fixed first; the operator is chosen after the method
--   - encoding: "under the same setup as Theorem 6.1", including the constant C_p depending only on p → its own ∃ C > 0 quantified after p and before L_p, R, N, n, the starting point and the method; the hypotheses 0 < L, 0 < R, 0 < N, 2N + 1 ≤ n written out; reason: both bounds remain true when C is decreased, so a single constant for Theorems 6.1 and 6.4 exists (the minimum of the two) iff each has its own; the setup's hypotheses are copied
--   - encoding: (p−1)-times continuously differentiable with L_p-Lipschitz D^{p−1} → Assumption51 p L F (ContDiff ℝ (p−1) F ∧ ‖iteratedFDeriv ℝ (p−1) F z − iteratedFDeriv ℝ (p−1) F z′‖ ≤ L‖z − z′‖); reason: the same two conditions; the operator norm of iteratedFDeriv is the induced multilinear norm
--   - encoding: nonexpansive operator T → IsNonexpansive T (the published predicate ‖T x − T y‖ ≤ ‖x − y‖); reason: the same condition
--   - encoding: a fixed point y∗ satisfying ‖y₀ − y∗‖ ≤ R → ∃ ystar, T ystar = ystar ∧ ‖y0 − ystar‖ ≤ R; reason: existence only, as in the source (no uniqueness claimed)
--   - encoding: ‖y_N − T(y_N)‖ ≥ min(R/(2(N + 1)), C_p L_p R^p/(N + 1)^{(3p−1)/2}) → min (R / (2 * ((N : ℝ) + 1))) (C * L * R ^ p / ((N : ℝ) + 1) ^ ((3p − 1)/2)) ≤ ‖methodIterate M y0 T N − T (methodIterate M y0 T N)‖; reason: the exponent is a real power
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Theorem 6.4, p.14

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_AnchoredEP_Assumption51
import Definitions.Def_AnchoredEP_Supplement_PthOrderMethod
import Definitions.Def_AnchoredEP_Supplement_methodIterate

open ThreeOpSplitting.Convergence

namespace AnchoredEP.Supplement

/-- **Theorem 6.4 (lower bound for `p`th-order methods on nonexpansive fixed-point problems).**
Jiang–Yoon, arXiv:2609.30212, Theorem 6.4, p.14: "Under the same setup as Theorem 6.1, for every
deterministic `p`th-order method initialized at `y₀`, there exists a `(p − 1)`-times continuously
differentiable and nonexpansive operator `T : ℝ^n → ℝ^n` with a fixed point `y∗` satisfying
`‖y₀ − y∗‖ ≤ R` such that `D^{p−1}T` is `L_p`-Lipschitz, for which the output of the algorithm after
`N` oracle queries satisfies
`‖y_N − T(y_N)‖ ≥ min(R/(2(N + 1)), C_p L_p R^p/(N + 1)^{(3p−1)/2})`. (30)"

The setup of Theorem 6.1 (p.12): `p ≥ 2` fixed, a constant `C_p > 0` depending only on `p`,
`L_p > 0`, `R > 0`, positive integers `N, n` with `n ≥ 2N + 1`, and a fixed starting point.

**Formalization Note.** The method `M : PthOrderMethod p n` sees `T` only through the oracle
outputs `D^jT(y_s)`, `0 ≤ j ≤ p − 1` (p.12, "with oracle outputs `D^jF` replaced with `D^jT`");
the output after `N` queries is `y_N = methodIterate M y0 T N`. Smoothness is the published
`Assumption51 p L T`; nonexpansiveness is the published `IsNonexpansive T`
(`‖T x − T y‖ ≤ ‖x − y‖`). `C_p` is its own existential constant depending only on `p`.
`(N + 1)^{(3p−1)/2}` is `Real.rpow`. -/
theorem theorem_6_4 (p : ℕ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L R : ℝ) (N n : ℕ), 0 < L → 0 < R → 0 < N → 2 * N + 1 ≤ n →
      ∀ (y0 : EuclideanSpace ℝ (Fin n)) (M : PthOrderMethod p n),
      ∃ T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Assumption51 p L T ∧
        IsNonexpansive T ∧
        (∃ ystar : EuclideanSpace ℝ (Fin n), T ystar = ystar ∧ ‖y0 - ystar‖ ≤ R) ∧
        min (R / (2 * ((N : ℝ) + 1))) (C * L * R ^ p / ((N : ℝ) + 1) ^ ((3 * (p : ℝ) - 1) / 2)) ≤
          ‖methodIterate M y0 T N - T (methodIterate M y0 T N)‖ := by sorry

end AnchoredEP.Supplement
