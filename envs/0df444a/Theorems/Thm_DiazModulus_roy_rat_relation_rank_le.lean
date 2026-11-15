-- Prove2me | Theorems.Thm_DiazModulus_roy_rat_relation_rank_le
-- name    : DiazModulus.roy_rat_relation_rank_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:39.080197+00:00
-- url     : https://prove2.me/theorems/30e473c1-16b7-457c-b02d-3fa461f8b00e
-- title:
--   Over ℚ, at lifts zⱼ = bⱼ + λⱼ with bⱼ ∈ ℚᵈ and λⱼ ∈ ℒᵈ, the relations of DALAG Th. 11.21 have ℚ-rank at most dim_ℚ(span_ℚ z ∩ span_ℚ(T + 2πiℚᵈ)), T = span(V′ ∩ ℚᵈ) + L₁
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic). A vector of $\mathbb C^d$ is *rational* if its coordinates are rational numbers, and a subspace $S \subseteq \mathbb C^d$ is *rational over $\mathbb Q$* if it is spanned by its rational vectors.
--
--   Let $z_1, \dots, z_\ell \in \mathbb C^d$ be linearly independent over $\mathbb Q$, with $z_j = b_j + \lambda_j$, $b_j \in \mathbb Q^d$ and $\lambda_j \in \mathcal L^d$. Let $V' \subseteq \mathbb C^d$ be any subspace and $L_1$ the common kernel of integer linear forms $\varphi_1, \dots, \varphi_q$ on $\mathbb C^d$. Let $\rho$ be the dimension of the $\mathbb Q$-span of the integer vectors $s \in \mathbb Z^\ell$ with $\sum_j s_j b_j \in V'$ and $\prod_i \big(\prod_j e^{s_j \lambda_{j,i}}\big)^{\varphi_{k,i}} = 1$ for every $k$ (the relation group of DALAG Th. 11.21 at these lifts). With $T = \mathrm{span}_{\mathbb C}(V' \cap \mathbb Q^d) + L_1$,
--   $$\rho \le \dim_{\mathbb Q} \Big(\mathrm{span}_{\mathbb Q}(z) \cap \mathrm{span}_{\mathbb Q}\{\tau + 2\pi i\,\kappa : \tau \in T,\ \kappa \in \mathbb Q^d\}\Big).$$
-- source:
--   Step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4, over F = ℚ (Remark (i), p. 37, with ℚ + ℒ in place of ℒ̃), in the setting of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2, with m = 1; the analogue over ℚ of DiazModulus.roy_relation_rank_le. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_rat_relation_rank_le {d ℓ q : ℕ} (z : Fin ℓ → Fin d → ℂ) (hzind : LinearIndependent ℚ z)
    (η : Fin ℓ → (Fin d → ℂ) × (Fin d → ℂ))
    (hη1 : ∀ j i, ∃ r : ℚ, (η j).1 i = (r : ℂ)) (hη2 : ∀ j i, (η j).2 i ∈ LogAlg)
    (hηz : ∀ j, (η j).1 + (η j).2 = z j)
    (V' : Submodule ℂ (Fin d → ℂ)) (φ : Fin q → Fin d → ℤ) (L₁ : Submodule ℂ (Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
          ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) ≤
      Module.finrank ℚ ↥(Submodule.span ℚ (Set.range z) ⊓
        Submodule.span ℚ {x : Fin d → ℂ |
          ∃ τ ∈ Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, ∃ r : ℚ, v i = (r : ℂ)} ⊔ L₁,
            ∃ κ : Fin d → ℂ, (∀ i, ∃ r : ℚ, κ i = (r : ℂ)) ∧
              x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ}) := by
  sorry

end DiazModulus
