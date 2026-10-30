-- Prove2me | Theorems.Thm_DiazModulus_torus_reduced_inf_eq_bot
-- name    : DiazModulus.torus_reduced_inf_eq_bot
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:05:42.459996+00:00
-- url     : https://prove2.me/theorems/b0f11ec8-70dc-43dc-b76f-1e028eab47d4
-- title:
--   No nonzero combination of reduced monomials $X^a Y^b Z^c$, with $\min(b_i, c_i) = 0$, lies in the torus ideal $(Y_i Z_i - 1)_i$
-- statement:
--   Let $K$ be a field and $A_0, A_1$ types, and let $K[X, Y, Z]$ be the polynomial ring over $K$ in the variables $X_h$ ($h \in A_0$) and $Y_i, Z_i$ ($i \in A_1$). The per-coordinate box `torusBox K A₀ A₁ T`, for $T \in \mathbb{N}^{A_0 \sqcup A_1}$, is the span of the monomials $X^a Y^b Z^c$ with $a_h \le T_h$ for every $h$ and $b_i + c_i \le T_i$ for every $i$; $J_0 = (Y_i Z_i - 1)_{i \in A_1}$ is the torus ideal `torusIdeal K A₀ A₁`, the kernel of $K[X, Y, Z] \to K[\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}]$; a monomial $X^a Y^b Z^c$ is reduced when $\min(b_i, c_i) = 0$ for every $i$ (`torusReduced`). Then the $K$-span of the reduced monomials meets $J_0$ only in $0$. No hypothesis on $K$ is needed. The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Let $\rho$ be the $K$-linear map $X^m \mapsto X^{\mathrm{red}(m)}$, with the reduced form of the previous node. Since $\mathrm{red}$ does not change when $b_i$ and $c_i$ both go up by one, $\rho(q\,Y_i Z_i) = \rho(q)$ for every $q$, so $\rho$ vanishes on $J_0$; and $\rho$ is the identity on combinations of reduced monomials. So a reduced combination in $J_0$ equals its image under $\rho$, which is $0$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical (normal forms modulo YZ − 1). The ring K[X, Y, Z] and its ideal are those of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.3.1 (Chapter 8 is by D. Roy), for K[G]. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem torus_reduced_inf_eq_bot {K A₀ A₁ : Type*} [Field K] :
    MvPolynomial.restrictSupport K (torusReduced A₀ A₁)
      ⊓ Submodule.restrictScalars K (torusIdeal K A₀ A₁) = ⊥ := by
  sorry

end DiazModulus
