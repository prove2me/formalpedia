-- Prove2me | Theorems.Thm_DiazModulus_eval_torusDerivList_eq_zero
-- name    : DiazModulus.eval_torusDerivList_eq_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:51:58.725385+00:00
-- url     : https://prove2.me/theorems/27871988-ac5e-4238-9a30-d9f8173a5787
-- title:
--   The premise of the multiplicity estimate: $D_{w_1} \cdots D_{w_t} P_c$ vanishes at $g_s$ for all $w_i \in W$, $t \le d M_0$ and $|s_j| \le d M_1$
-- statement:
--   Let $A_0, A_1$ be finite types and $R = \mathbb{C}[X, Y, Z]$ the polynomial ring `MvPolynomial (A₀ ⊕ (A₁ × Bool)) ℂ` in the variables $X_h$ ($h \in A_0$), $Y_i$ and $Z_i$ ($i \in A_1$), and $J_0 = (Y_iZ_i - 1)_{i \in A_1}$ its torus ideal (`torusIdeal`). Write $G = \mathbb{G}_a^{A_0} \times \mathbb{G}_m^{A_1}$ (`TorusGroup`: pairs $g = (x, y)$, $x$ in the additive group $\mathbb{C}^{A_0}$, $y \in (\mathbb{C}^\times)^{A_1}$, written multiplicatively), and say that a polynomial vanishes at $g$ when it vanishes at the point $(x, y, y^{-1})$ (`torusPt g`). For $w = (\xi, \eta) \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$, $D_w$ (`torusDeriv w`) is the invariant derivation $\sum_h \xi_h\,\partial/\partial X_h + \sum_i \eta_i (Y_i\,\partial/\partial Y_i - Z_i\,\partial/\partial Z_i)$ of $R$ (DALAG Lemma 8.11), and $D_l = D_{w_1} \circ \cdots \circ D_{w_t}$ (`torusDerivList l`) for a list $l = [w_1, \dots, w_t]$. For $u_j \in \mathbb{C}^{A_0}$, $a_{ji} \in \mathbb{C}^\times$ ($j \in B_1$, $i \in A_1$, $B_1$ finite) and $s \in \mathbb{Z}^{B_1}$, $g_s = (\sum_j s_j u_j, (\prod_j a_{ji}^{s_j})_i) \in G$ (`hmePoint u a s`). Let $B_0$ be a type, $w_b \in \mathbb{C}^{A_0} \times \mathbb{C}^{A_1}$ ($b \in B_0$) with span $W$, $D_0, D_1, M_0, M_1 \in \mathbb{N}$, $d = |A_0| + |A_1|$, coefficients $c$ and $P_c$ as in `torusCoeffPoly`, and assume the premise of the Definition `MultiplicityEstimateElem` for the complex numbers $a_{ji}$: for every $r \le dM_0$, every $k_1, \dots, k_r \in B_0$ and every $s \in \mathbb{Z}^{B_1}$ with $|s_j| \le dM_1$, $\sum_\lambda c_\lambda (\mathrm{Op}^\lambda_{w_{k_1}} \cdots \mathrm{Op}^\lambda_{w_{k_r}} X^\tau)(\sum_j s_j u_j) \prod_i (\prod_j a_{ji}^{s_j})^{t_i - D_1} = 0$, with $\mathrm{Op}^\lambda_w$ as in `DiazModulus.eval_torusDerivList_torusCoeffPoly`. Then $D_l P_c$ vanishes at $g_s$ for every list $l$ of elements of $W$ of length at most $dM_0$ and every $s$ with $|s_j| \le dM_1$. The names `TorusGroup`, `torusPt`, `torusDeriv`, `torusDerivList`, `torusTransl`, `torusVanishing`, `torusZero`, `torusStab`, `standardSet`, `sectionIdeal`, `vanishOrd`, `hmePoint` and `obstructionSpan` come from the Definition `DiazMultiplicity` (module `Definitions.Def_DiazMultiplicity`), which builds on the published Definition `DiazHilbertBox` (`torusIdeal`, `torusBox`, `boxHilb`, `boxD`, `torusCoeffPoly`, `torusReduced`, `torusPoint`).
--
--   **Proof.** By `DiazModulus.eval_torusDerivList_torusCoeffPoly` the premise says that evaluation at $g_s$ kills $D_{w_{k_1}} \cdots D_{w_{k_n}} P_c$ for $n \le dM_0$, hence the span $V_n$ of these. Since $w \mapsto D_w$ is linear, $D_w V_n \subseteq V_{n+1}$ for $w \in W$, so $D_l P_c \in V_{|l|}$.
--
--   **Novelty.** None claimed: the premise of Theorem 8.1, read on the invariant derivations of DALAG, Chapter 8 (by D. Roy), written at finite level and in coordinates; routine formalisation.
-- source:
--   M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Chapter 8 (by D. Roy), Th. 8.1 (§8.1): the vanishing hypothesis, for $G = \mathbb{G}_a^{d_0} \times \mathbb{G}_m^{d_1}$. Uses `DiazModulus.eval_torusDerivList_torusCoeffPoly`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazMultiplicity

namespace DiazModulus

theorem eval_torusDerivList_eq_zero {A₀ A₁ B₀ B₁ : Type*} [Fintype A₀] [Fintype A₁] [Fintype B₁]
    [DecidableEq A₀] [DecidableEq A₁]
    (wₑ : B₀ → (A₀ → ℂ) × (A₁ → ℂ)) (uₑ : B₁ → A₀ → ℂ) (aₑ : B₁ → A₁ → ℂ) (D₀ D₁ M₀ M₁ : ℕ)
    (cₑ : (A₀ → Fin (D₀ + 1)) × (A₁ → Fin (2 * D₁ + 1)) → ℂ)
    (a : B₁ → A₁ → ℂˣ) (ha : ∀ j i, (a j i : ℂ) = aₑ j i)
    (hprem : (∀ (rₑ : ℕ) (kₑ : Fin rₑ → B₀) (sₑ : B₁ → ℤ), rₑ ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ j, |sₑ j| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        ∑ l, cₑ l * (MvPolynomial.eval (∑ j, ((sₑ j : ℤ) : ℂ) • uₑ j)
          ((List.ofFn fun k : Fin rₑ =>
            ((∑ h, (wₑ (kₑ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (wₑ (kₑ k)).2 i * (((l.2 i : ℕ) : ℂ) - D₁)) • LinearMap.id :
                Module.End ℂ (MvPolynomial A₀ ℂ)))).prod
            (∏ h, MvPolynomial.X h ^ (l.1 h : ℕ)))
        * ∏ i, (∏ j, aₑ j i ^ sₑ j) ^ (((l.2 i : ℕ) : ℤ) - D₁)) = 0)) :
    ∀ l : List ((A₀ → ℂ) × (A₁ → ℂ)), l.length ≤ (Fintype.card A₀ + Fintype.card A₁) * M₀ → (∀ w ∈ l, w ∈ Submodule.span ℂ (Set.range wₑ)) →
      ∀ s : B₁ → ℤ, (∀ b, |s b| ≤ (((Fintype.card A₀ + Fintype.card A₁) * M₁ : ℕ) : ℤ)) →
        MvPolynomial.eval (torusPt (hmePoint uₑ a s)) (torusDerivList l (torusCoeffPoly D₀ D₁ cₑ)) = 0 := by
  sorry

end DiazModulus
