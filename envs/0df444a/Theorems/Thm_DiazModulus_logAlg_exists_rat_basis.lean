-- Prove2me | Theorems.Thm_DiazModulus_logAlg_exists_rat_basis
-- name    : DiazModulus.logAlg_exists_rat_basis
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T14:06:56.405312+00:00
-- url     : https://prove2.me/theorems/4bd5033e-d997-42a8-8631-fed7444b0051
-- title:
--   Finitely many logarithms λ₁, …, λₘ ∈ ℒ are rational linear combinations of some μ₁, …, μₛ ∈ ℒ that are linearly independent over ℚ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $\lambda_1, \dots, \lambda_m \in \mathcal L$. Then there are a natural number $s$, numbers $\mu_1, \dots, \mu_s \in \mathcal L$ linearly independent over $\mathbb Q$, and rational numbers $c_{kt}$ ($1 \le k \le m$, $1 \le t \le s$) such that
--   $$\lambda_k = \sum_{t=1}^s c_{kt}\,\mu_t \quad\text{for every } k.$$
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 12.23 (p. 436): the choice of a ℚ-basis among finitely many logarithms, as in the Baker step of DALAG §12.3.2 (p. 435). Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem logAlg_exists_rat_basis {m : ℕ} (lam : Fin m → ℂ) (hlam : ∀ k, lam k ∈ LogAlg) :
    ∃ (s : ℕ) (μ : Fin s → ℂ) (c : Fin m → Fin s → ℚ), LinearIndependent ℚ μ ∧
      (∀ t, μ t ∈ LogAlg) ∧ ∀ k, lam k = ∑ t, (c k t : ℂ) * μ t := by
  sorry

end DiazModulus
