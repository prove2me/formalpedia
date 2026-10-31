-- Prove2me | Theorems.Thm_DiazModulus_eval_torusDerivList_torusCoeffPoly
-- name    : DiazModulus.eval_torusDerivList_torusCoeffPoly
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:10.103691+00:00
-- url     : https://prove2.me/theorems/7f625dfe-5f9a-4702-9aac-d8d7d9227e20
-- title:
--   The value at a torus point of $D_{w_1} \cdots D_{w_r} P_c$ is the coordinate sum of the multiplicity estimate's premise
-- statement:
--   Let $K$ be a field. Let $A_0, A_1$ be finite types and $R = K[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) K` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). For $w = (\xi, \eta) \in K^{A_0} \times K^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. Let $D_0, D_1 \in \mathbb{N}$, let $c$ be a family of coefficients in $K$ indexed by the pairs $\lambda = (\tau, t)$ with $\tau \in \{0, \dots, D_0\}^{A_0}$ and $t \in \{0, \dots, 2D_1\}^{A_1}$, and $P_c$ = `torusCoeffPoly D₀ D₁ c` $= \sum_\lambda c_\lambda X^\tau \prod_i Y_i^{(t_i - D_1)_+} Z_i^{(D_1 - t_i)_+}$. For $w = (\xi, \eta)$ and $\lambda$ let $\mathrm{Op}^\lambda_w = \sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (t_i - D_1)$, a linear operator on $K[X_{A_0}]$. Then for $w_1, \dots, w_r$, $x \in K^{A_0}$ and $y \in (K^\times)^{A_1}$, the value of $D_{w_1} \cdots D_{w_r} P_c$ at $(x, y, y^{-1})$ is $\sum_\lambda c_\lambda\, (\mathrm{Op}^\lambda_{w_1} \cdots \mathrm{Op}^\lambda_{w_r} X^\tau)(x)\, \prod_i y_i^{t_i - D_1}$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** $D_w$ acts on $X$-polynomials as $\sum_h \xi_h \partial/\partial X_h$, and the Laurent monomial $\prod_i Y_i^{(t_i - D_1)_+} Z_i^{(D_1 - t_i)_+}$ is an eigenvector of $D_w$ with eigenvalue $\sum_i \eta_i (t_i - D_1)$; Leibniz and induction on the list, then evaluation.
--
--   **Novelty.** None claimed: the coordinate form of the premise of Theorem 8.1 of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), §8.1 and Lemma 8.11: the derivatives $D_{w_1} \cdots D_{w_r} P$ of the premise of Th. 8.1. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem eval_torusDerivList_torusCoeffPoly {K A₀ A₁ : Type*} [Field K] [Fintype A₀] [Fintype A₁] [DecidableEq A₀] [DecidableEq A₁]
    (D₀ D₁ : ℕ) (c : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → K) (r : ℕ)
    (w : Fin r → (A₀ → K) × (A₁ → K)) (x : A₀ → K) (y : A₁ → Kˣ) :
    MvPolynomial.eval (torusPoint x y) (torusDerivList (List.ofFn w) (torusCoeffPoly D₀ D₁ c))
      = ∑ l, c l * (MvPolynomial.eval x
          ((List.ofFn fun k : Fin r =>
            ((∑ h, (w k).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w k).2 i * (((l.2 i : ℕ) : K) - D₁)) • LinearMap.id :
                Module.End K (MvPolynomial A₀ K)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (y i : K) ^ (((l.2 i : ℕ) : ℤ) - D₁)) := by
  sorry

end DiazModulus
