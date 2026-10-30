-- Prove2me | Theorems.Thm_DiazModulus_boxHilb_torusIdeal
-- name    : DiazModulus.boxHilb_torusIdeal
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T08:04:35.61614+00:00
-- url     : https://prove2.me/theorems/ba355a95-d2ed-4260-a008-eb8c9d75c400
-- title:
--   The Hilbert function of the torus ideal on per-coordinate boxes: $h_{J_0}(T) = \prod_h (T_h + 1) \cdot \prod_i (2T_i + 1)$
-- statement:
--   Let $K$ be a field and $A_0, A_1$ types, and let $K[X, Y, Z]$ be the polynomial ring over $K$ in the variables $X_h$ ($h \in A_0$) and $Y_i, Z_i$ ($i \in A_1$). The per-coordinate box `torusBox K A₀ A₁ T`, for $T \in \mathbb{N}^{A_0 \sqcup A_1}$, is the span of the monomials $X^a Y^b Z^c$ with $a_h \le T_h$ for every $h$ and $b_i + c_i \le T_i$ for every $i$; $J_0 = (Y_i Z_i - 1)_{i \in A_1}$ is the torus ideal `torusIdeal K A₀ A₁`, the kernel of $K[X, Y, Z] \to K[\mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}]$; a monomial $X^a Y^b Z^c$ is reduced when $\min(b_i, c_i) = 0$ for every $i$ (`torusReduced`). Assume that $A_0$ and $A_1$ are finite. Then for every $T \in \mathbb{N}^{A_0 \sqcup A_1}$, $h_{J_0}(T) = \prod_{h \in A_0} (T_h + 1) \cdot \prod_{i \in A_1} (2T_i + 1)$, where $h_{J_0}(T)$ is `boxHilb (torusBox K A₀ A₁) (torusIdeal K A₀ A₁) T`, the dimension of the image of the box $T$ in $K[X, Y, Z]/J_0$. The names `boxHilb`, `blockBox`, `torusBox`, `torusIdeal`, `torusList`, `torusReduced`, `boxD`, `torusCoeffPoly`, `torusPoint` and `UnmixedHeight` are those of the published Definition `DiazHilbertBox` (module `Definitions.Def_DiazHilbertBox`).
--
--   **Proof.** Let $\mathcal{B}$ be the box (finite-dimensional by `DiazModulus.restrictSupport_block_filtration`) and $R$ the span of the reduced monomials. By `DiazModulus.torus_reduce_mem_restrictSupport`, $\mathcal{B} = (\mathcal{B} \cap R) + (\mathcal{B} \cap J_0)$, and by `DiazModulus.torus_reduced_inf_eq_bot` the two pieces meet in $0$; with `DiazModulus.boxHilb_add_finrank_inf`, $h_{J_0}(T) = \dim (\mathcal{B} \cap R)$, the number of reduced exponents in the box. These are $X^a Y^b Z^c$ with $a_h \le T_h$, $b_i + c_i \le T_i$ and $\min(b_i, c_i) = 0$, and $(b_i, c_i) \mapsto T_i + b_i - c_i$ is a bijection onto $\{0, \dots, 2T_i\}$.
--
--   **Novelty.** Not found in the sources read in this form; routine. DALAG Prop. 5.7 gives the Hilbert function of $G = \mathbb{G}_a^{d_0} \times \mathbb{G}_m^{d_1}$ for the total degree in the $X$ variables; here the box is per coordinate.
-- source:
--   Compare M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Prop. 5.7 (§5.3.1, p. 159; Chapter 5 is by D. Roy), the case G* = G, there with the total degree in the additive variables; the passage to K[X, Y, Z] is that of §8.3.1 (Chapter 8 is by D. Roy). Not found in the sources read in this form; routine. Uses DiazModulus.restrictSupport_block_filtration, DiazModulus.torus_reduce_mem_restrictSupport, DiazModulus.torus_reduced_inf_eq_bot and DiazModulus.boxHilb_add_finrank_inf. C1.1 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazHilbertBox

namespace DiazModulus

theorem boxHilb_torusIdeal {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] (T : A₀ ⊕ A₁ → ℕ) :
    boxHilb (torusBox K A₀ A₁) (torusIdeal K A₀ A₁) T
      = (∏ h, (T (Sum.inl h) + 1)) * ∏ i, (2 * T (Sum.inr i) + 1) := by
  sorry

end DiazModulus
