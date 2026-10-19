-- Prove2me | Theorems.Thm_DiazModulus_laurent_window_quadratic_pencils_carry_no_three_factors
-- name    : DiazModulus.laurent_window_quadratic_pencils_carry_no_three_factors
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:51.658894+00:00
-- url     : https://prove2.me/theorems/979360f2-518a-4b14-a602-96ba0c4aba9c
-- title:
--   If every non-zero f in a plane M has ord f ≤ N − 2 and deg f ≥ N + 2, the pencils (1, X² + αX) and (X + β, X² + γX), β ≠ 0, carry no three free factors in H_N + M
-- statement:
--   Let $K$ be a field, $N \geq 0$, $H_N = \mathrm{span}_K(X^{N-1}, X^N, X^{N+1}) \subseteq K[X]$, and $M \subseteq K[X]$ a subspace of dimension $2$ such that every non-zero $f \in M$ has $\operatorname{ord} f + 2 \leq N$ and $\deg f \geq N + 2$, where $\operatorname{ord} f$ is the order of $f$ at $0$ (its trailing degree). Put $W = H_N + M$. Then:
--
--   - for no $\alpha \in K$ are there linearly independent $b_0, b_1, b_2 \in K[X]$ with $b_j \in W$ and $(X^2 + \alpha X)b_j \in W$ for all $j$;
--   - for no $\beta, \gamma \in K$ with $\beta \neq 0$ are there linearly independent $b_0, b_1, b_2 \in K[X]$ with $(X + \beta)b_j \in W$ and $(X^2 + \gamma X)b_j \in W$ for all $j$.
--
--   **Proof.** An element of $W$ divisible by $X^{N-1}$ lies in $H_N$, since otherwise its $M$-part would be divisible by $X^{N-1}$, against the order bound. Given one of the pencils $(p, q)$ and free $b_j$ with $pb_j, qb_j \in W$, `DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line` ($\deg p < \deg q$) puts the 3-space $Y = \mathrm{span}(pb_0, pb_1, pb_2)$ in $H_N + Kn$, so $\dim(Y \cap H_N) \geq 2$. But if $py \in Y \cap H_N$, then $X^{N-1} \mid y$ (for $p = X + \beta$ because $X^{N-1}$ is coprime to $p$), so $X^{N-1} \mid qy$; then $qy \in H_N$ has degree at most $N + 1$, and $\deg q = 2$ forces $y \in KX^{N-1}$. So $Y \cap H_N$ is at most a line, a contradiction.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_window_quadratic_pencils_carry_no_three_factors (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) :
    (∀ α : K, ¬ ∃ b : Fin 3 → K[X], LinearIndependent K b ∧ ∀ j, b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
          (X ^ 2 + C α * X) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) ∧
    (∀ β γ : K, β ≠ 0 → ¬ ∃ b : Fin 3 → K[X], LinearIndependent K b ∧ ∀ j, (X + C β) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
          (X ^ 2 + C γ * X) * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) := by
  sorry

end DiazModulus
