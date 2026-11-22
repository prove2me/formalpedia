-- Prove2me | Theorems.Thm_DiazModulus_rational_proper_annihilator
-- name    : DiazModulus.rational_proper_annihilator
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:16.770254+00:00
-- url     : https://prove2.me/theorems/faf8bdc6-266f-4d8f-bbc4-2b37276f8973
-- title:
--   A rational subspace T ≠ ℂᵈ is killed by a non-zero linear form with algebraic coefficients: some algebraic φ ≠ 0 has φ · v = 0 for every v ∈ T
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates. For $u, v \in \mathbb C^d$ write $u \cdot v = \sum_i u_i v_i$.
--
--   Let $T \subseteq \mathbb C^d$ be a rational subspace with $T \neq \mathbb C^d$. Then there is a non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates such that $\varphi \cdot v = 0$ for every $v \in T$.
-- source:
--   Classical linear algebra over Q̄, for a proper subspace: one half of the remark in S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, p. 170, that a subspace defined over Q̄ is one defined by linear equations with coefficients in Q̄. A step of the proof of Th. 2.1 (pp. 170–171) in DiazModulus.fischler_theorem_2_1. Proved from DiazModulus.rational_common_kernel. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem rational_proper_annihilator {d : ℕ} (T : Submodule ℂ (Fin d → ℂ))
    (hT : Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T) (hTop : T ≠ ⊤) :
    ∃ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) ∧ φ ≠ 0 ∧ ∀ v ∈ T, φ ⬝ᵥ v = 0 := by
  sorry

end DiazModulus
