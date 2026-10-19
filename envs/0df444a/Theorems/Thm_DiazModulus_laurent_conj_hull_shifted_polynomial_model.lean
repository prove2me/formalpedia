-- Prove2me | Theorems.Thm_DiazModulus_laurent_conj_hull_shifted_polynomial_model
-- name    : DiazModulus.laurent_conj_hull_shifted_polynomial_model
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-18T14:28:24.758557+00:00
-- url     : https://prove2.me/theorems/589b61c2-de42-4c0a-8a8f-99119687bf57
-- title:
--   A five-dimensional hull span(1, v, v̄, z, z̄) of a Laurent polynomial z without v² P(v) in it is the image of H_N + M under F ↦ F(v)/v^N, with M two-sided
-- statement:
--   Let $v \in \mathbb{C} \setminus \overline{\mathbb{Q}}$ with $v\bar v = 1$. Let $k \geq 0$, let $c_j \in \overline{\mathbb{Q}}$ for all $j \in \mathbb{Z}$, and put $z = \sum_{j=-k}^{k} c_jv^j$ and $W = \mathrm{span}_{\overline{\mathbb{Q}}}(1, v, \bar v, z, \bar z)$. Suppose $\dim_{\overline{\mathbb{Q}}} W = 5$ and $W$ contains no $v^2P(v)$ with $P \in \overline{\mathbb{Q}}[X]$ non-zero. Then there are $N \geq 3$ and a subspace $M \subseteq \overline{\mathbb{Q}}[X]$ of dimension $2$ such that, with $H_N = \mathrm{span}_{\overline{\mathbb{Q}}}(X^{N-1}, X^N, X^{N+1})$:
--
--   - no element of $M$ has a term in $X^{N-1}$, $X^N$ or $X^{N+1}$;
--   - every non-zero $f \in M$ has $\operatorname{ord} f + 2 \leq N$ and $\deg f \geq N + 2$, where $\operatorname{ord} f$ is the order of $f$ at $0$ (its trailing degree);
--   - a polynomial $F \in \overline{\mathbb{Q}}[X]$ has $F(v)/v^N \in W$ if and only if $F \in H_N + M$;
--   - every $w \in W$ is $F(v)/v^N$ for some $F \in H_N + M$.
--
--   **Proof.** Take $N = k + 3$ and $\varphi(F) = F(v)/v^N$, a $\overline{\mathbb{Q}}$-linear map $\overline{\mathbb{Q}}[X] \to \mathbb{C}$, injective because $v$ is transcendental. It sends $X^{N-1}, X^N, X^{N+1}$ to $\bar v, 1, v$, $F_L = \sum c_jX^{j+N}$ to $z$ and $F_R = \sum \bar c_jX^{N-j}$ to $\bar z$ (as $\bar v = 1/v$); with $\pi$ deleting the coefficients at $N - 1, N, N + 1$, put $M = \mathrm{span}(\pi F_L, \pi F_R)$, which has no such terms. Then $\varphi$ maps $H_N + M$ onto $W$, which with injectivity gives the equivalence, and $5 = \dim W \leq 3 + \dim M \leq 5$ gives $\dim M = 2$. For the order bound, a non-zero $f \in M$ of order at least $N - 1$ is $X^{N+2}P$ with $\varphi(f) = v^2P(v) \in W$, so $P = 0$; for the degree bound, a non-zero $f \in M$ of degree at most $N + 1$ has $\overline{\varphi(f)} = v^2R(v) \in W$, with $R$ the reflection of the conjugate of $f$ about $N - 2$, and again $R = 0$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. R18 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 18 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem laurent_conj_hull_shifted_polynomial_model
    (v : ℂ) (hv : v ∉ Qbar) (hv1 : v * conj v = 1) (k : ℕ) (c : ℤ → ℂ) (hc : ∀ j, c j ∈ Qbar)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ)) = 5)
    (hB : ∀ P : Polynomial ↥Qbar, v ^ 2 * Polynomial.aeval v P ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) → P = 0) :
    ∃ (N : ℕ) (M : Submodule (↥Qbar) (↥Qbar)[X]), 3 ≤ N ∧ Module.finrank (↥Qbar) M = 2 ∧
      (∀ f ∈ M, f.coeff (N - 1) = 0 ∧ f.coeff N = 0 ∧ f.coeff (N + 1) = 0) ∧
      (∀ f ∈ M, f ≠ 0 → f.natTrailingDegree + 2 ≤ N) ∧ (∀ f ∈ M, f ≠ 0 → N + 2 ≤ f.natDegree) ∧
      (∀ F : (↥Qbar)[X], aeval v F / v ^ N ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ) ↔
        F ∈ Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) ⊔ M) ∧
      ∀ w ∈ Submodule.span Qbar ({1, v, conj v, (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j), conj (∑ j ∈ Finset.Icc (-(k : ℤ)) k, c j * v ^ j)} : Set ℂ),
        ∃ F ∈ Submodule.span (↥Qbar) ({X ^ (N - 1), X ^ N, X ^ (N + 1)} : Set (↥Qbar)[X]) ⊔ M,
          aeval v F / v ^ N = w := by
  sorry

end DiazModulus
