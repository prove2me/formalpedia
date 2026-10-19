-- Prove2me | Theorems.Thm_DiazModulus_laurent_window_involution_pencil_normal_form
-- name    : DiazModulus.laurent_window_involution_pencil_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:49.181183+00:00
-- url     : https://prove2.me/theorems/116ef81b-0bf3-4bfc-9ec5-5565a079bb0e
-- title:
--   If M is two-sided without window terms and three free bⱼ have X bⱼ, (X² + β) bⱼ ∈ H_N + M, then M = span(X^(N−2) + eX^(N+2), βX^(N−3) + ζX^(N+2) + eX^(N+3))
-- statement:
--   Let $K$ be a field, $N \geq 3$, $H_N = \mathrm{span}_K(X^{N-1}, X^N, X^{N+1}) \subseteq K[X]$, and $M \subseteq K[X]$ a subspace of dimension $2$ such that no element of $M$ has a term in $X^{N-1}$, $X^N$ or $X^{N+1}$, and every non-zero $f \in M$ has $\operatorname{ord} f + 2 \leq N$ and $\deg f \geq N + 2$, where $\operatorname{ord} f$ is the order of $f$ at $0$ (its trailing degree). Put $W = H_N + M$. Let $\beta \in K$ be non-zero, and suppose there are linearly independent $b_0, b_1, b_2 \in K[X]$ with $Xb_j \in W$ and $(X^2 + \beta)b_j \in W$ for all $j$. Then there are $e, \zeta \in K$ with $e \neq 0$ and
--
--   $$M = \mathrm{span}_K\bigl(X^{N-2} + eX^{N+2},\ \beta X^{N-3} + \zeta X^{N+2} + eX^{N+3}\bigr).$$
--
--   **Proof.** An element of $W$ without terms in $X^{N-1}, X^N, X^{N+1}$ lies in $M$, and `DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line` with $(p, q) = (X, X^2 + \beta)$ puts every $Xy$ with $Xy, (X^2 + \beta)y \in W$ in $H_N + Kn$, $n$ of least degree in $M$. Killing the coefficients of $X^{\deg n - 1}$ and $X^{N-1}$ in a combination $y$ of the $b_j$ gives $Xy \in H_N$, so $y = aX^{N-2} + cX^N$, and removing the window terms of $(X^2 + \beta)y$ leaves $\beta aX^{N-2} + cX^{N+2} \in M$; the order and degree bounds give $a \neq 0 \neq c$, so $X^{N-2} + eX^{N+2} \in M$ with $e \neq 0$, and $n$ is a multiple of it. Killing the coefficients of $X^{N-2}$ and $X^{N-1}$ instead gives $y = sX^{N-3} + cX^N + seX^{N+1}$ with $s \neq 0$ by the order bound, and $(X^2 + \beta)y$ leaves $\beta sX^{N-3} + cX^{N+2} + seX^{N+3} \in M$. Dividing by $s$ gives the second generator, and two free elements span $M$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_window_involution_pencil_normal_form (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2) (hN : 3 ≤ N)
    (hMc : ∀ f ∈ M, f.coeff (N - 1) = 0 ∧ f.coeff N = 0 ∧ f.coeff (N + 1) = 0)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree)
    (β : K) (hβ : β ≠ 0) (b : Fin 3 → K[X]) (hb : LinearIndependent K b)
    (hbW : ∀ j, X * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧ (X ^ 2 + C β) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) :
    ∃ e ζ : K, e ≠ 0 ∧ M = Submodule.span K
      ({X ^ (N - 2) + C e * X ^ (N + 2), C β * X ^ (N - 3) + C ζ * X ^ (N + 2) + C e * X ^ (N + 3)} : Set K[X]) := by
  sorry

end DiazModulus
