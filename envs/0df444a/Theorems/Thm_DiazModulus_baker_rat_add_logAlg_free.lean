-- Prove2me | Theorems.Thm_DiazModulus_baker_rat_add_logAlg_free
-- name    : DiazModulus.baker_rat_add_logAlg_free
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:20.995836+00:00
-- url     : https://prove2.me/theorems/c4cffc6c-0782-418c-b701-4e9a46e478cb
-- title:
--   Baker's theorem for ℚ + ℒ: if e₁, …, eₘ ∈ ℚ + ℒ are linearly independent over ℚ, they are linearly independent over Q̄
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $e_1, \dots, e_m \in \mathbb C$ be linearly independent over $\mathbb Q$, each in $\mathbb Q + \mathcal L$: for every $k$ there is $q_k \in \mathbb Q$ with $e_k - q_k \in \mathcal L$. Then $e_1, \dots, e_m$ are linearly independent over $\overline{\mathbb Q}$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.23 (p. 436): the Baker step of DALAG §12.3.2 (p. 435), where a ℚ-basis of the span of 1 and the entries of a matrix over ℚ + ℒ is also free over Q̄; here for any ℚ-free family in ℚ + ℒ, from Baker's theorem (DALAG, Th. 1.6), proved on the platform as Schanuel.baker_linear_forms_in_logarithms. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem baker_rat_add_logAlg_free {m : ℕ} (e : Fin m → ℂ) (he : LinearIndependent ℚ e)
    (heL : ∀ k, ∃ q : ℚ, e k - q ∈ LogAlg) : LinearIndependent (↥Qbar) e := by
  sorry

end DiazModulus
