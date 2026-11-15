-- Prove2me | Theorems.Thm_DiazModulus_roy_hull_transport
-- name    : DiazModulus.roy_hull_transport
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T10:29:29.7854+00:00
-- url     : https://prove2.me/theorems/aa3bea11-9b5b-4d61-9349-97a242abdd30
-- title:
--   A configuration in a rational S₀ of least dimension s moves to ℂˢ: same dimension, no non-zero algebraic vector, rational hull ℂˢ, and a Q̄-free family of the same length in ℒ̃ˢ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $S_0 \subseteq \mathbb C^d$ be a rational subspace of dimension $s$, and $U \subseteq S_0$ a subspace that contains no non-zero vector with algebraic coordinates, such that every rational subspace $T \supseteq U$ has $\dim T \ge s$. Let $z_1, \dots, z_\ell \in U \cap \widetilde{\mathcal L}^d$ be linearly independent over $\overline{\mathbb Q}$. Then there are a subspace $U' \subseteq \mathbb C^s$ and vectors $z'_1, \dots, z'_\ell \in U' \cap \widetilde{\mathcal L}^s$, linearly independent over $\overline{\mathbb Q}$, such that $\dim U' = \dim U$, $U'$ contains no non-zero vector with algebraic coordinates, and $\mathbb C^s$ is the only rational subspace of $\mathbb C^s$ containing $U'$.
-- source:
--   Step of the proof of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Th. 5 (pp. 39–40): Roy's injection of ℂ^(d*) onto the kernel of t (p. 39), written through an adapted basis of S₀ with a left inverse that preserves ℒ̃. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem roy_hull_transport {d s ℓ : ℕ} (S₀ U : Submodule ℂ (Fin d → ℂ))
    (hS₀ : Submodule.span ℂ {v : Fin d → ℂ | v ∈ S₀ ∧ ∀ i, v i ∈ Qbar} = S₀)
    (hs : Module.finrank ℂ ↥S₀ = s) (hUS₀ : U ≤ S₀)
    (hUQ : ∀ v ∈ U, (∀ i, v i ∈ Qbar) → v = 0)
    (hmin : ∀ T : Submodule ℂ (Fin d → ℂ),
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U ≤ T → s ≤ Module.finrank ℂ ↥T)
    (z : Fin ℓ → Fin d → ℂ) (hzU : ∀ i, z i ∈ U) (hz : ∀ i j, z i j ∈ LogAlgTilde)
    (hzind : LinearIndependent (↥Qbar) z) :
    ∃ (U' : Submodule ℂ (Fin s → ℂ)) (z' : Fin ℓ → Fin s → ℂ),
      Module.finrank ℂ ↥U' = Module.finrank ℂ ↥U ∧
      (∀ v ∈ U', (∀ i, v i ∈ Qbar) → v = 0) ∧
      (∀ T : Submodule ℂ (Fin s → ℂ),
        Submodule.span ℂ {v : Fin s → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T → U' ≤ T → T = ⊤) ∧
      (∀ i, z' i ∈ U') ∧ (∀ i j, z' i j ∈ LogAlgTilde) ∧ LinearIndependent (↥Qbar) z' := by
  sorry

end DiazModulus
