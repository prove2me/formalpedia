-- Prove2me | Theorems.Thm_DiazModulus_torus_coeff_poly
-- name    : DiazModulus.torus_coeff_poly
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:05:12.523012+00:00
-- url     : https://prove2.me/theorems/933cb638-27e5-431a-945b-80dac0905c2f
-- title:
--   A coefficient vector $c$ on the box $(D_0; D_1)$ gives $P_c$ in that box, outside the torus ideal if $c \ne 0$, with $P_c(x, y, y^{-1}) = \sum c_{\tau,s}\, x^\tau \prod_i y_i^{s_i - D_1}$
-- statement:
--   Let $K$ be a field and $A_0, A_1$ types, and let $K[X, Y, Z]$ be the polynomial ring over $K$ in the variables $X_h$ ($h \in A_0$) and $Y_i, Z_i$ ($i \in A_1$). The per-coordinate box `torusBox K A₀ A₁ T`, for $T \in \mathbb{N}^{A_0 \sqcup A_1}$, is the span of the monomials $X^a Y^b Z^c$ with $a_h \le T_h$ for every $h$ and $b_i + c_i \le T_i$ for every $i$; $J_0 = (Y_i Z_i - 1)_{i \in A_1}$ is the torus ideal `torusIdeal K A₀ A₁`, the kernel of $K[X, Y, Z] \to K[\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}]$; a monomial $X^a Y^b Z^c$ is reduced when $\min(b_i, c_i) = 0$ for every $i$ (`torusReduced`). Assume that $A_0$ and $A_1$ are finite, let $D_0, D_1 \in \mathbb{N}$, and let $c$ be a family of elements of $K$ indexed by the pairs $(\tau, s)$ with $\tau \in \{0, \dots, D_0\}^{A_0}$ and $s \in \{0, \dots, 2D_1\}^{A_1}$. Let $P_c$ be `torusCoeffPoly D₀ D₁ c`, that is $P_c = \sum_{\tau, s} c_{\tau,s}\, X^\tau \prod_i Y_i^{(s_i - D_1)_+} Z_i^{(D_1 - s_i)_+}$, with $(\cdot)_+$ the positive part. Then (i) $P_c$ lies in the box `boxD A₀ A₁ D₀ D₁` ($X_h$-degree at most $D_0$, $\deg_{Y_i} + \deg_{Z_i}$ at most $D_1$); (ii) if $c \ne 0$ then $P_c \notin J_0$; (iii) for every $x \in K^{A_0}$ and $y \in (K^\times)^{A_1}$, the value of $P_c$ at the point `torusPoint x y` $= (x, y, y^{-1})$ is $\sum_{\tau, s} c_{\tau,s} \prod_h x_h^{\tau_h} \prod_i y_i^{s_i - D_1}$, with the integer exponents $s_i - D_1 \in \{-D_1, \dots, D_1\}$. The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** (i) Each monomial of $P_c$ has $X_h$-degree $\tau_h \le D_0$ and $(Y_i, Z_i)$-degree $(s_i - D_1)_+ + (D_1 - s_i)_+ = |s_i - D_1| \le D_1$. (ii) The monomials of $P_c$ are reduced, since one of the two positive parts vanishes, and distinct $(\tau, s)$ give distinct monomials, since $s_i = D_1 + (s_i - D_1)_+ - (D_1 - s_i)_+$; so if $P_c \in J_0$, `DiazModulus.torus_reduced_inf_eq_bot` gives $P_c = 0$ and every $c_{\tau,s}$, a coefficient of $P_c$, is $0$. (iii) Evaluation is a ring map, and $y_i^{(s_i - D_1)_+} (y_i^{-1})^{(D_1 - s_i)_+} = y_i^{s_i - D_1}$.
--
--   **Novelty.** Not found in the sources read in this form; routine. Bookkeeping that puts a coefficient vector on the box of the multiplicity estimate into the model.
-- source:
--   The polynomials P = Σ c X^τ Y^t of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Th. 8.1 (§8.1, p. 232; Chapter 8 is by D. Roy), for G = 𝔾ₐ^(A₀) × 𝔾ₘ^(A₁), written in K[X, Y, Z] as in §8.3.1. Not found in the sources read in this form; routine. Uses DiazModulus.torus_reduced_inf_eq_bot. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem torus_coeff_poly {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁]
    [DecidableEq A₀] [DecidableEq A₁] (D₀ D₁ : ℕ) (c : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → K) :
    torusCoeffPoly D₀ D₁ c ∈ torusBox K A₀ A₁ (boxD A₀ A₁ D₀ D₁) ∧
    (c ≠ 0 → torusCoeffPoly D₀ D₁ c ∉ torusIdeal K A₀ A₁) ∧
    ∀ (x : A₀ → K) (y : A₁ → Kˣ), MvPolynomial.eval (torusPoint x y) (torusCoeffPoly D₀ D₁ c)
      = ∑ l, c l * ((∏ h, x h ^ (l.1 h : ℕ)) * ∏ i, (y i : K) ^ (((l.2 i : ℕ) : ℤ) - D₁)) := by
  sorry

end DiazModulus
