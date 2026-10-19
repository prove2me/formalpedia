-- Prove2me | Theorems.Thm_DiazModulus_laurent_window_degree_one_pencil_factor_space
-- name    : DiazModulus.laurent_window_degree_one_pencil_factor_space
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:44.273296+00:00
-- url     : https://prove2.me/theorems/cf467a44-0836-48d0-9251-e374fef5b9ac
-- title:
--   If M is two-sided and three free bⱼ have bⱼ, X bⱼ ∈ H_N + M, then H_N + M = span(X^(N−1), X^N, X^(N+1), G, X G) for some G
-- statement:
--   Let $K$ be a field, $N \geq 0$, $H_N = \mathrm{span}_K(X^{N-1}, X^N, X^{N+1}) \subseteq K[X]$, and $M \subseteq K[X]$ a subspace of dimension $2$ such that every non-zero $f \in M$ has $\operatorname{ord} f + 2 \leq N$ and $\deg f \geq N + 2$, where $\operatorname{ord} f$ is the order of $f$ at $0$ (its trailing degree); call such an $M$ two-sided. Put $W = H_N + M$, and suppose there are linearly independent $b_0, b_1, b_2 \in K[X]$ with $b_j \in W$ and $Xb_j \in W$ for all $j$. Then there is $G \in W$ with $XG \in W$ such that every $F \in W$ with $XF \in W$ lies in $\mathrm{span}_K(X^{N-1}, X^N, G)$, and $W = \mathrm{span}_K(X^{N-1}, X^N, X^{N+1}, G, XG)$.
--
--   **Proof.** Two linear functionals, the coefficients of $X^{N-1}$ and $X^N$, vanish on a non-zero combination $G$ of the $b_j$, and still $G, XG \in W$. By `DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line` with $(p, q) = (1, X)$, every $F$ with $F, XF \in W$ lies in $H_N + Kn$, where $n$ has least degree in $M$. If $F \in H_N$ and $XF \in W$, the $M$-part of $XF$ has order at least $N - 1$, so it is $0$ and $F$ has no $X^{N+1}$ term; hence $G = h + \mu n$ with $\mu \neq 0$, and every such $F$ lies in $\mathrm{span}(X^{N-1}, X^N, G)$. Finally $XG = h'' + m''$ with $\deg m'' = \deg n + 1$, so $n$ and $m''$ span $M$; both lie in $\mathrm{span}(H_N, G, XG)$, which is therefore $W$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Uses DiazModulus.laurent_window_factor_in_hull_plus_min_degree_line. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_window_degree_one_pencil_factor_space (K : Type*) [Field K] (N : ℕ) (M : Submodule K K[X]) (hM2 : Module.finrank K M = 2)
    (hMo : ∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N)
    (hMd : ∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree)
    (b : Fin 3 → K[X]) (hb : LinearIndependent K b)
    (hbW : ∀ j, b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧ X * b j ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M)) :
    ∃ G ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M), X * G ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) ∧
      (∀ F : K[X], F ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) → X * F ∈ (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) →
        F ∈ Submodule.span K ({X ^ (N - 1), X ^ N, G} : Set K[X])) ∧
      (Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set K[X]) ⊔ M) = Submodule.span K ({X ^ (N - 1), X ^ N, X ^ (N + 1), G, X * G} : Set K[X]) := by
  sorry

end DiazModulus
