-- Prove2me | Theorems.Thm_DiazModulus_roy_relation_rank_le
-- name    : DiazModulus.roy_relation_rank_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-13T09:51:07.213265+00:00
-- url     : https://prove2.me/theorems/aff18692-108b-48a2-a7c6-3453be6e876e
-- title:
--   At Roy's lifts, the relations of DALAG Th. 11.21 have $\mathbb Q$-rank at most $m \dim(\mathrm{span}\,z \cap (T + 2\pi i\,\overline{\mathbb Q}^d))$ for T = Υ(span(V′ ∩ Q̄ᵈ) × L₁)
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $\omega \in \mathbb C^m$, $\Upsilon : \mathbb C^d \times \mathbb C^{m \times d} \to \mathbb C^d$ is Roy's map $\Upsilon(x, y)_i = x_i + \sum_{k=1}^m \omega_k y_{k,i}$ (DALAG §11.6.2), and $\Upsilon_1(y) = \Upsilon(0, y)$.
--
--   Let $\omega$ be algebraic and $\mathbb Q$-free, $z_1, \dots, z_\ell \in \mathbb C^d$ linearly independent over $\overline{\mathbb Q}$, and $\eta_{b,i} \in k^d \times \mathcal L^{m \times d}$ with $\Upsilon(\eta_{b,i}) = \omega_b z_i$, where $k$ is the $\mathbb Q$-span of $\omega$. Let $V' \subseteq \mathbb C^d$ be any subspace and $L_1$ the common kernel of integer linear forms $\varphi_1, \dots, \varphi_q$. Let $\rho$ be the $\mathbb Q$-rank of the integer vectors $s$ with $\sum s_j \eta_j' \in V'$ and $\prod_i \big(\prod_j e^{s_j \eta_{j,i}''}\big)^{\varphi_{k,i}} = 1$ for every $k$ (the relation group of DALAG Th. 11.21). With $T = \Upsilon\big(\mathrm{span}_{\mathbb C}(V' \cap \overline{\mathbb Q}^d) \times L_1\big)$:
--   $$\rho \le m \cdot \dim_{\overline{\mathbb Q}} \Big(\mathrm{span}_{\overline{\mathbb Q}}(z) \cap \{\tau + 2\pi i\,\kappa : \tau \in T,\ \kappa \in \overline{\mathbb Q}^d\}\Big).$$
-- source:
--   Step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 4, in the setting of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §11.6.2. The route is the Diaz modulus mission's: an induction on d that splits along a rational subspace of maximal slope and applies DALAG Th. 11.21 once at each semistable step, counting the periods through one extra rational subspace; DALAG and Roy argue instead through Th. 11.5 (3′) and Lemma 11.24, respectively Roy's Th. 2. Not found in the sources read in this form; routine. Formal proof: Diaz modulus mission, 13 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_relation_rank_le {d m ℓ q : ℕ} (ω : Fin m → ℂ) (hωQ : LinearIndependent ℚ ω)
    (hωalg : ∀ a, ω a ∈ Qbar) (hω1 : (1 : ℂ) ∈ Submodule.span ℚ (Set.range ω))
    (hωmul : ∀ a b, ω a * ω b ∈ Submodule.span ℚ (Set.range ω))
    (z : Fin ℓ → Fin d → ℂ) (hzind : LinearIndependent (↥Qbar) z)
    (η : Fin m × Fin ℓ → (Fin d → ℂ) × (Fin m × Fin d → ℂ))
    (hη1 : ∀ p i, (η p).1 i ∈ Submodule.span ℚ (Set.range ω)) (hη2 : ∀ p r, (η p).2 r ∈ LogAlg)
    (hηΥ : ∀ p, (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)) (η p) = ω p.1 • z p.2)
    (V' : Submodule ℂ (Fin d → ℂ)) (φ : Fin q → Fin m × Fin d → ℤ) (L₁ : Submodule ℂ (Fin m × Fin d → ℂ))
    (hL₁ : ∀ v, v ∈ L₁ ↔ ∀ k, ∑ i, (φ k i : ℂ) * v i = 0) :
    Module.finrank ℚ ↥(Submodule.span ℚ ((fun s : Fin m × Fin ℓ → ℤ => fun j => (s j : ℚ)) ''
        {s : Fin m × Fin ℓ → ℤ | (∑ j, (s j : ℂ) • (η j).1) ∈ V' ∧
            ∀ k, ∏ i, (∏ j, Complex.exp ((η j).2 i) ^ s j) ^ φ k i = 1})) ≤
      m * Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range z) ⊓
        Submodule.span (↥Qbar) {x : Fin d → ℂ | ∃ τ ∈ ((Submodule.span ℂ {v : Fin d → ℂ | v ∈ V' ∧ ∀ i, v i ∈ Qbar}).prod L₁).map (LinearMap.pi fun i : Fin d =>
        (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ LinearMap.fst ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)
        + ∑ k, ω k • (LinearMap.proj (k, i) : (Fin m × Fin d → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
            LinearMap.snd ℂ (Fin d → ℂ) (Fin m × Fin d → ℂ)),
          ∃ κ : Fin d → ℂ, (∀ i, κ i ∈ Qbar) ∧ x = τ + (2 * (Real.pi : ℂ) * Complex.I) • κ}) := by
  sorry

end DiazModulus
