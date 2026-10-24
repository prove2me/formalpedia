-- Prove2me | Theorems.Thm_DiazModulus_quadratic_complement_eigen_forms
-- name    : DiazModulus.quadratic_complement_eigen_forms
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:39.615572+00:00
-- url     : https://prove2.me/theorems/606b4fc0-36c9-4193-bca8-0dcf958516cf
-- title:
--   If P(u)/Q(u), of degree 2, maps g₀, g₁ into span(1, u, u⁻¹, g₀, g₁) of dimension 5, that span is complete, two-orbit or cyclic
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $P, Q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg P, \deg Q) = 2$, and let $g_0, g_1 \in \mathbb{C}$ be such that $S = \mathrm{span}(1, u, u^{-1}, g_0, g_1)$ has dimension $5$ and $(P(u)/Q(u))\,g_j \in S$ for $j = 0, 1$. Write $P_c = P(u) - cQ(u)$. Then one of the following holds:
--
--   - **(scalar)** for some $c \in \overline{\mathbb{Q}}$, $Q(u)R(u)/(uP_c) \in S$ for every $R \in \overline{\mathbb{Q}}[X]$ of degree at most $2$;
--   - **(two-orbit)** for some $c_1 \neq c_2$ in $\overline{\mathbb{Q}}$ and $R_1, R_2 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$, $S = \mathrm{span}(1, u, u^{-1}, Q(u)R_1(u)/(uP_{c_1}), Q(u)R_2(u)/(uP_{c_2}))$;
--   - **(cyclic)** for some $c \in \overline{\mathbb{Q}}$ and $R_0, R_1 \in \overline{\mathbb{Q}}[X]$ of degree at most $2$, $S = \mathrm{span}(1, u, u^{-1}, Q(u)R_0(u)/(uP_c), Q(u)(Q(u)R_0(u) + P_cR_1(u))/(uP_c^2))$.
--
--   **Proof.** Coprimality and degree give $Q \neq 0$ and $P - cQ \neq 0$, so $Q(u) \neq 0$ and $P_c \neq 0$. Let $k = P(u)/Q(u)$. `DiazModulus.quadratic_complement_multiplication_matrix` gives $T$ over $\overline{\mathbb{Q}}$ and $R_0, R_1$ of degree at most $2$ with $kg_j = R_j(u)/u + \sum_iT_{ij}g_i$. With $G(x) = x_0g_0 + x_1g_1$ and $H(x) = x_0R_0 + x_1R_1$ this reads $kG(x) = H(x)(u)/u + G(Tx)$, so $Tx = cx + y$ gives $G(x) = Q(u)(H(x)(u) + uG(y))/(uP_c)$. Apply `DiazModulus.qbar_matrix_fin_two_eigen_or_jordan` to $T$. Eigenvectors $v, w$ for $c_1 \neq c_2$: $G(v)$, $G(w)$ have the two-orbit form with $R_1 = H(v)$, $R_2 = H(w)$, and as $v, w$ span $\overline{\mathbb{Q}}^2$, $\mathrm{span}(1, u, u^{-1}, G(v), G(w)) = S$. A Jordan pair: $G(v)$ as above and $G(w) = Q(u)(Q(u)H(v)(u) + P_cH(w)(u))/(uP_c^2)$, the cyclic form, with the same span. Scalar $T = cI$: multiplication by $k - c = P_c/Q(u)$ sends $g_0, g_1, Q(u)/u$ to $R_0(u)/u, R_1(u)/u, (P - cQ)(u)/u$, which are independent because $g_0, g_1, Q(u)/u$ are (the five generators of $S$ are), so they span the three-dimensional $H_0$. Every $R(u)/u$ is then $(k - c)(\alpha_0g_0 + \alpha_1g_1 + \alpha_2Q(u)/u)$, and $Q(u)R(u)/(uP_c) = \alpha_0g_0 + \alpha_1g_1 + \alpha_2Q(u)/u \in S$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Step 4 of the sheaf-free proof of Theorem NF. Uses DiazModulus.qbar_matrix_fin_two_eigen_or_jordan and DiazModulus.quadratic_complement_multiplication_matrix. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_complement_eigen_forms (u : ℂ) (hu : u ∉ Qbar) (P Q : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (g : Fin 2 → ℂ)
    (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) = 5)
    (hk : ∀ j, aeval u P / aeval u Q * g j ∈ Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) :
    (∃ c : ↥Qbar, ∀ R : (↥Qbar)[X], R.natDegree ≤ 2 → aeval u Q * aeval u R / (u * (aeval u P - (c : ℂ) * aeval u Q)) ∈
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ)) ∨
    (∃ c₁ c₂ : ↥Qbar, c₁ ≠ c₂ ∧ ∃ R₁ R₂ : (↥Qbar)[X], R₁.natDegree ≤ 2 ∧ R₂.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₁ / (u * (aeval u P - (c₁ : ℂ) * aeval u Q)),
          aeval u Q * aeval u R₂ / (u * (aeval u P - (c₂ : ℂ) * aeval u Q))} : Set ℂ)) ∨
    (∃ c : ↥Qbar, ∃ R₀ R₁ : (↥Qbar)[X], R₀.natDegree ≤ 2 ∧ R₁.natDegree ≤ 2 ∧
        Submodule.span Qbar ({1, u, u⁻¹, g 0, g 1} : Set ℂ) = Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u R₀ / (u * (aeval u P - (c : ℂ) * aeval u Q)),
          aeval u Q * (aeval u Q * aeval u R₀ + (aeval u P - (c : ℂ) * aeval u Q) * aeval u R₁) / (u * (aeval u P - (c : ℂ) * aeval u Q) ^ 2)} :
            Set ℂ)) := by
  sorry

end DiazModulus
