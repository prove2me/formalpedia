-- Prove2me | Theorems.Thm_DiazModulus_quadratic_ratio_pole_fractions_independent
-- name    : DiazModulus.quadratic_ratio_pole_fractions_independent
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-23T07:19:54.295164+00:00
-- url     : https://prove2.me/theorems/ba7a6c98-36b5-4799-aec7-d07d9355836d
-- title:
--   For a ratio h of degree 2, pole fractions q(αq + βJ)/(u(p − λq)) at three distinct λ are linearly independent modulo span(1, u, u⁻¹)
-- statement:
--   Let $u \in \mathbb{C}$ be transcendental, that is, $u \notin \overline{\mathbb{Q}}$ (the algebraic numbers); spans and linear independence are over $\overline{\mathbb{Q}}$. Let $p, q \in \overline{\mathbb{Q}}[X]$ be coprime with $\max(\deg p, \deg q) = 2$, and $J = p'q - pq'$. Let $\lambda_0, \lambda_1, \lambda_2 \in \overline{\mathbb{Q}}$ be distinct, let $\alpha_i, \beta_i \in \overline{\mathbb{Q}}$ with $(\alpha_i, \beta_i) \neq (0, 0)$ for each $i$, and put $g_i = q(u)(\alpha_iq(u) + \beta_iJ(u))/(u(p(u) - \lambda_iq(u)))$. If $a, b, c, d_0, d_1, d_2 \in \overline{\mathbb{Q}}$ satisfy $a + bu + cu^{-1} + d_0g_0 + d_1g_1 + d_2g_2 = 0$, then $a = b = c = 0$ and $d_0 = d_1 = d_2 = 0$.
--
--   So $1, u, u^{-1}, g_0, g_1, g_2$ are linearly independent: pole fractions at three distinct values of $\lambda$ are independent modulo $H_0 = \mathrm{span}(1, u, u^{-1})$.
--
--   **Proof.** The denominators are non-zero: $u \neq 0$, and $p - \lambda q \neq 0$ by coprimality and degree, so its value at the transcendental $u$ is not $0$. Write $h = p(u)/q(u)$ and $w = J(u)/q(u)$, so that $g_i = (q(u)/u)(\alpha_i + \beta_iw)/(h - \lambda_i)$. The $H_0$-part $a + bu + cu^{-1}$ is $R(u)/u$ with $R = c + aX + bX^2$, and `DiazModulus.quadratic_pencil_wronskian_span` writes $R = a'q + b'p + c'J$. Dividing the relation by $q(u)/u$ and multiplying by $\prod_j(h - \lambda_j)$ gives $A(h) + B(h)w = 0$ with $A = (a' + b'X)\Pi + \sum_id_i\alpha_i\Pi_i$ and $B = c'\Pi + \sum_id_i\beta_i\Pi_i$, where $\Pi = \prod_j(X - \lambda_j)$ and $\Pi_i = \prod_{j \neq i}(X - \lambda_j)$. Then `DiazModulus.quadratic_ratio_wronskian_free` gives $A = B = 0$. Evaluating at $X = \lambda_i$, where $\Pi_i(\lambda_i) \neq 0$ as the $\lambda_j$ are distinct and every other term vanishes, leaves $d_i\alpha_i = d_i\beta_i = 0$, so $d_i = 0$. Then $a + bu + cu^{-1} = 0$, and $a = b = c = 0$ because $c + aX + bX^2$ vanishes at $u$.
--
--   **Novelty.** Not found in the sources read; routine.
-- source:
--   Not found in the sources read. Step 1 of the sheaf-free proof of Theorem NF. Uses DiazModulus.quadratic_pencil_wronskian_span and DiazModulus.quadratic_ratio_wronskian_free. R20 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 23 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

open Polynomial in
theorem quadratic_ratio_pole_fractions_independent (u : ℂ) (hu : u ∉ Qbar) (p q : (↥Qbar)[X])
    (hcop : IsCoprime p q) (hdeg : max p.natDegree q.natDegree = 2)
    (l α β : Fin 3 → ↥Qbar) (hl : Function.Injective l) (hαβ : ∀ i, α i ≠ 0 ∨ β i ≠ 0)
    (a b c : ↥Qbar) (d : Fin 3 → ↥Qbar)
    (hrel : (a : ℂ) + (b : ℂ) * u + (c : ℂ) * u⁻¹ + ∑ i, (d i : ℂ) *
        (aeval u q * ((α i : ℂ) * aeval u q + (β i : ℂ) * aeval u (derivative p * q - p * derivative q)) /
          (u * (aeval u p - (l i : ℂ) * aeval u q))) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  sorry

end DiazModulus
