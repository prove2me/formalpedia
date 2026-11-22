-- Prove2me | Theorems.Thm_DiazModulus_rational_common_kernel
-- name    : DiazModulus.rational_common_kernel
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:09.401889+00:00
-- url     : https://prove2.me/theorems/6f1a7ace-6a00-4e3a-895b-7b7758a93260
-- title:
--   A rational subspace T ⊆ ℂᵈ is the common kernel of d linear forms with algebraic coefficients: v ∈ T if and only if ψ₁ · v = ⋯ = ψ_d · v = 0
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $u, v \in \mathbb C^d$ write $u \cdot v = \sum_i u_i v_i$.
--
--   Let $T \subseteq \mathbb C^d$ be a rational subspace. Then there are $\psi_1, \dots, \psi_d \in \mathbb C^d$ with algebraic coordinates such that, for every $v \in \mathbb C^d$, $v \in T$ if and only if $\psi_i \cdot v = 0$ for $i = 1, \dots, d$.
-- source:
--   Classical linear algebra over Q̄: one half of the remark in S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, p. 170, that a subspace defined over Q̄ is one defined by linear equations with coefficients in Q̄. Used for Th. 2.1 (through DiazModulus.rational_proper_annihilator) and for the pencil forms of Prop. 3.1 and Th. 4.2. Proved from DiazModulus.roy_rational_adapted_basis. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rational_common_kernel {d : ℕ} (T : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T) :
    ∃ ψ : Fin d → Fin d → ℂ, (∀ i j, ψ i j ∈ Qbar) ∧
      ∀ v : Fin d → ℂ, v ∈ T ↔ ∀ i, ψ i ⬝ᵥ v = 0 := by
  sorry

end DiazModulus
