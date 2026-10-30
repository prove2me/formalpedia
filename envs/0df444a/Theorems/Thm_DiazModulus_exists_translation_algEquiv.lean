-- Prove2me | Theorems.Thm_DiazModulus_exists_translation_algEquiv
-- name    : DiazModulus.exists_translation_algEquiv
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:44.545005+00:00
-- url     : https://prove2.me/theorems/8d749754-5bc6-4c85-854c-2e0115d34b6a
-- title:
--   Translation by $(x, y) \in K^{A_0} \times (K^\times)^{A_1}$ is an automorphism of $K[X, Y, Z]$ that preserves every per-coordinate box and the torus ideal
-- statement:
--   Let $K$ be a field and $A_0, A_1$ types, and let $K[X, Y, Z]$ be the polynomial ring over $K$ in the variables $X_h$ ($h \in A_0$) and $Y_i, Z_i$ ($i \in A_1$). The per-coordinate box `torusBox K A₀ A₁ T`, for $T \in \mathbb{N}^{A_0 \sqcup A_1}$, is the span of the monomials $X^a Y^b Z^c$ with $a_h \le T_h$ for every $h$ and $b_i + c_i \le T_i$ for every $i$; $J_0 = (Y_i Z_i - 1)_{i \in A_1}$ is the torus ideal `torusIdeal K A₀ A₁`, the kernel of $K[X, Y, Z] \to K[\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}]$; a monomial $X^a Y^b Z^c$ is reduced when $\min(b_i, c_i) = 0$ for every $i$ (`torusReduced`). Let $x \in K^{A_0}$ and $y \in (K^\times)^{A_1}$. Then there is a $K$-algebra automorphism $e$ of $K[X, Y, Z]$ with $e(X_h) = X_h + x_h$, $e(Y_i) = y_i Y_i$ and $e(Z_i) = y_i^{-1} Z_i$, which maps every per-coordinate box onto itself and maps $J_0$ onto itself ($e(J_0) = J_0$). The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Define $e$ on the variables and its inverse by $X_h \mapsto X_h - x_h$, $Y_i \mapsto y_i^{-1} Y_i$, $Z_i \mapsto y_i Z_i$. Each sends a monomial $X^m$ into the span of the monomials with exponent $\le m$; every box is a lower set of exponents, so it is mapped into itself by both, hence onto itself. Finally $e(Y_i Z_i - 1) = y_i y_i^{-1} Y_i Z_i - 1 = Y_i Z_i - 1$.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical. Translations of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §5.3.2 (Chapter 5 is by D. Roy), written on K[X, Y, Z] as in §8.3.1 (Chapter 8 is by D. Roy). C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem exists_translation_algEquiv {K A₀ A₁ : Type*} [Field K] (x : A₀ → K) (y : A₁ → Kˣ) :
    ∃ e : MvPolynomial (A₀ ⊕ (A₁ × Bool)) K ≃ₐ[K] MvPolynomial (A₀ ⊕ (A₁ × Bool)) K,
      (∀ v, e (MvPolynomial.X v) = Sum.elim (fun h => MvPolynomial.X (Sum.inl h) + MvPolynomial.C (x h))
        (fun p : A₁ × Bool => MvPolynomial.C (torusPoint x y (Sum.inr p)) * MvPolynomial.X (Sum.inr p)) v) ∧
      (∀ T : A₀ ⊕ A₁ → ℕ, (torusBox K A₀ A₁ T).map e.toLinearMap = torusBox K A₀ A₁ T) ∧
      (torusIdeal K A₀ A₁).map e = torusIdeal K A₀ A₁ := by
  sorry

end DiazModulus
