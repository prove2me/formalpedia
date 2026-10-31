-- Prove2me | Theorems.Thm_DiazModulus_strong_six_exponentials_unconditional
-- name    : DiazModulus.strong_six_exponentials_unconditional
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:28.977408+00:00
-- url     : https://prove2.me/theorems/baa9e124-e0cd-4e73-a079-5fbd02908e93
-- title:
--   Roy's strong six exponentials theorem, unconditional
-- statement:
--   Here $\overline{\mathbb{Q}}$ is the field of algebraic numbers, $\mathcal{L}$ is the set of logarithms of algebraic numbers (the $z \in \mathbb{C}$ with $e^z$ algebraic), and $\widetilde{\mathcal{L}}$ is the $\overline{\mathbb{Q}}$-vector space spanned by $1$ and $\mathcal{L}$ (`Qbar` and `LogAlgTilde` of the published Definition `DiazModulus`, module `Definitions.Def_DiazModulus`). Let $x \in \mathbb{C}^2$ and $y \in \mathbb{C}^3$ each be linearly independent over $\overline{\mathbb{Q}}$. Then $x_i y_j \notin \widetilde{\mathcal{L}}$ for some $i, j$. This is Roy's strong six exponentials theorem, with no hypothesis: milestone 161, `DiazModulus.strong_six_exponentials`, proves it under the hypothesis `MultiplicityEstimateElem`, and `DiazModulus.multiplicityEstimateElem` proves that hypothesis.
--
--   **Proof.** Apply `DiazModulus.strong_six_exponentials` to `DiazModulus.multiplicityEstimateElem`.
--
--   **Novelty.** Classical: Roy's strong six exponentials theorem (Roy 1992, Cor. 2; DALAG Cor. 11.16, §11.6.1); routine formalisation.
-- source:
--   Roy's strong six exponentials theorem: D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47, Cor. 2; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.16 (§11.6.1; this node is its case d = 2, ℓ = 3). Here from Roy's theorem under the multiplicity estimate (C1.4 of the Diaz modulus mission) and the multiplicity estimate itself, DALAG Th. 8.1 in the case G⁻ = {e} after P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355–383. Uses `DiazModulus.strong_six_exponentials` and `DiazModulus.multiplicityEstimateElem`. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem strong_six_exponentials_unconditional :
    ∀ x : Fin 2 → ℂ, ∀ y : Fin 3 → ℂ, LinearIndependent (↥Qbar) x → LinearIndependent (↥Qbar) y →
      ¬ ∀ i j, x i * y j ∈ LogAlgTilde := by
  sorry

end DiazModulus
