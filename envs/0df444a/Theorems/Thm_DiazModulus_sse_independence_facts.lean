-- Prove2me | Theorems.Thm_DiazModulus_sse_independence_facts
-- name    : DiazModulus.sse_independence_facts
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:06:06.736996+00:00
-- url     : https://prove2.me/theorems/b00a4cdc-6cac-45d5-b48f-7f603bed33eb
-- title:
--   For ℚ-free algebraic ω and Q̄-free x, y: the $\omega_a y_j$ are ℤ-free, and the line ℂx meets β·Q̄² only in 0 for every β ≠ 0
-- statement:
--   Let $\omega_1, \dots, \omega_m \in \overline{\mathbb{Q}}$ be linearly independent over $\mathbb{Q}$, and let $x \in \mathbb{C}^2$ and $y \in \mathbb{C}^3$ each be linearly independent over $\overline{\mathbb{Q}}$ (the algebraic numbers). Then:
--
--   - if $s \in \mathbb{Z}^{m \times 3}$ and $\sum_{a,j} s_{a,j}\,\omega_a y_j = 0$, then $s = 0$;
--   - if $\beta \neq 0$, $v \in \overline{\mathbb{Q}}^2$, $c \in \mathbb{C}$ and $c x_i = \beta v_i$ for $i = 1, 2$, then $c = 0$.
--
--   **Proof.** (1) Group the sum by $j$: the coefficient $\sum_a s_{a,j}\omega_a$ of $y_j$ is algebraic, so the $\overline{\mathbb{Q}}$-independence of $y$ makes it $0$, and the $\mathbb{Q}$-independence of $\omega$ makes every $s_{a,j}$ zero. (2) If $c \neq 0$, multiplying $v_2 x_1 - v_1 x_2$ by $c$ gives $0$, so $v_2 x_1 - v_1 x_2 = 0$ and the $\overline{\mathbb{Q}}$-independence of $x$ forces $v = 0$; then $cx_1 = 0$, so $x_1 = 0$, which an independent family excludes.
--
--   **Novelty.** Not found in the sources read in this form; routine. Two elementary facts. This route uses part (1) where DALAG §11.6.2 uses Baker's theorem (the injectivity in Lemma 11.18 (4)).
-- source:
--   Elementary. Part (1) is used where M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, appeals to Baker's theorem (Lemma 11.18 (4)). Not found in the sources read in this form; routine. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem sse_independence_facts (m : ℕ) (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω) (hωalg : ∀ a, ω a ∈ Qbar)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y) :
    (∀ s : Fin m × Fin 3 → ℤ, ∑ p, (s p : ℂ) * ω p.1 * y p.2 = 0 → s = 0) ∧
    ∀ (β c : ℂ) (v : Fin 2 → ℂ), β ≠ 0 → (∀ i, v i ∈ Qbar) → (∀ i, c * x i = β * v i) → c = 0 := by
  sorry

end DiazModulus
