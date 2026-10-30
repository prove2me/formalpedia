-- Prove2me | Theorems.Thm_DiazModulus_torus_reduce_mem_restrictSupport
-- name    : DiazModulus.torus_reduce_mem_restrictSupport
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:05:27.297452+00:00
-- url     : https://prove2.me/theorems/e88e21b7-927e-43d8-87d5-36a7931b156d
-- title:
--   Modulo the torus ideal $(Y_i Z_i - 1)_i$, every polynomial in a per-coordinate box is congruent to a combination of reduced monomials in the same box
-- statement:
--   Let $K$ be a field and $A_0, A_1$ types, and let $K[X, Y, Z]$ be the polynomial ring over $K$ in the variables $X_h$ ($h \in A_0$) and $Y_i, Z_i$ ($i \in A_1$). The per-coordinate box `torusBox K A₀ A₁ T`, for $T \in \mathbb{N}^{A_0 \sqcup A_1}$, is the span of the monomials $X^a Y^b Z^c$ with $a_h \le T_h$ for every $h$ and $b_i + c_i \le T_i$ for every $i$; $J_0 = (Y_i Z_i - 1)_{i \in A_1}$ is the torus ideal `torusIdeal K A₀ A₁`, the kernel of $K[X, Y, Z] \to K[\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}]$; a monomial $X^a Y^b Z^c$ is reduced when $\min(b_i, c_i) = 0$ for every $i$ (`torusReduced`). Then for every $T \in \mathbb{N}^{A_0 \sqcup A_1}$ and every $f$ in the box $T$ there is a $K$-linear combination $g$ of reduced monomials, also in the box $T$, with $f - g \in J_0$. The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** The reduced form of $X^a Y^b Z^c$ replaces each pair $(b_i, c_i)$ by $(\max(b_i - c_i, 0), \max(c_i - b_i, 0))$; it is reduced, it is coordinatewise below the original exponent, so it stays in the box, and it does not change when $b_i$ and $c_i$ both go up by one. By strong induction on the degree every monomial is congruent to its reduced form modulo $J_0$, since $X^{m'} Y_i Z_i - X^{m'} = X^{m'} (Y_i Z_i - 1)$. Take for $g$ the image of $f$ under $X^m \mapsto X^{\mathrm{red}(m)}$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical (normal forms modulo YZ − 1). The ring K[X, Y, Z] and its ideal are those of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.3.1 (Chapter 8 is by D. Roy), for K[G]. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem torus_reduce_mem_restrictSupport {K A₀ A₁ : Type*} [Field K] (T : A₀ ⊕ A₁ → ℕ) (f : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)
    (hf : f ∈ torusBox K A₀ A₁ T) :
    ∃ g ∈ torusBox K A₀ A₁ T ⊓ MvPolynomial.restrictSupport K (torusReduced A₀ A₁),
      f - g ∈ torusIdeal K A₀ A₁ := by
  sorry

end DiazModulus
