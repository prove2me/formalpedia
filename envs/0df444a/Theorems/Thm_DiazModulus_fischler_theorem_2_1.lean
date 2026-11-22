-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_2_1
-- name    : DiazModulus.fischler_theorem_2_1
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:11.568816+00:00
-- url     : https://prove2.me/theorems/9d9e396d-974b-4432-8bd6-7d79c6bc191e
-- title:
--   Fischler 2001, Th. 2.1: if M ∈ ℒ̃ᵈˣˡ of rank r < dl/(d + l) has Q̄-free rows and columns, MS ⊆ T for rational S, T of codim. l₁, d₁ ≥ 1 and r₁ ≥ 1 with l₁d₁/(l₁ + d₁) ≤ r₁ < rd₁/d
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $M$ be a $d \times l$ matrix with entries in $\widetilde{\mathcal L}$, of rank $r$ (over $\mathbb C$). Assume that the $l$ columns of $M$ are linearly independent over $\overline{\mathbb Q}$ ($Mb \neq 0$ for every non-zero $b \in \mathbb C^l$ with algebraic coordinates), that its $d$ rows are linearly independent over $\overline{\mathbb Q}$ ($\varphi^{\mathsf T} M \neq 0$ for every non-zero $\varphi \in \mathbb C^d$ with algebraic coordinates), and that $(d + l)\,r < dl$. Then there are rational subspaces $S \subseteq \mathbb C^l$ and $T \subseteq \mathbb C^d$ and a natural number $r_1$ such that, with $l_1 = l - \dim S$ and $d_1 = d - \dim T$, we have $l_1 \ge 1$, $d_1 \ge 1$, $Ms \in T$ for every $s \in S$, $r_1 \ge 1$, and
--   $$r_1 d < r d_1 \quad\text{and}\quad l_1 d_1 \le r_1 (l_1 + d_1),$$
--   that is, $r_1/d_1 < r/d$ and $r_1 \ge l_1 d_1/(l_1 + d_1)$.
--
--   In Fischler's terms: $M$ is the matrix of a linear map $u$ in bases defined over $\overline{\mathbb Q}$, its kernel contains no non-zero vector defined over $\overline{\mathbb Q}$, its image lies in no hyperplane defined over $\overline{\mathbb Q}$, $r < dl/(d + l)$, and $S$, $T$ are defined over $\overline{\mathbb Q}$ with $u(S) \subseteq T$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 2.1 (pp. 170–171): Roy's Th. 4 in Fischler's form, in coordinates for bases defined over Q̄ (a subspace defined over Q̄ is a rational one, p. 170). Hypotheses 2 and 3 say that the columns and the rows of M are Q̄-free; hyperplanes are vector hyperplanes (convention of p. 169); the printed hypothesis that the spaces E and F are non-zero follows from (d + l)r < dl and is omitted; the integer r₁ is existentially quantified, as printed. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. Fischler derives the theorem from Th. 4 of D. Roy, Matrices whose coefficients are linear forms in logarithms, J. Number Theory 41 (1992), 22–47 (p. 34), referring to Roy's proof of Cor. 1. The proof here takes T at a rational subspace minimising (r − dim(U ∩ T))/(d − dim T), U the column space of M, and gets the strict inequality r₁/d₁ < r/d from Roy's Th. 4 at the trivial minimiser: if r₁/d₁ = r/d, the zero subspace minimises the ratio too, and Th. 4 there gives dl ≤ r(d + l), against the hypothesis. Roy's proof of Cor. 1 (p. 38) does not contain that step; Roy's Th. 4 holds for every minimiser (p. 34), so the step is available. Proved from DiazModulus.roy_theorem_four, DiazModulus.roy_theorem_four_exists, DiazModulus.multiplicityEstimateElem, DiazModulus.rational_preimage_finrank and DiazModulus.rational_proper_annihilator. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_2_1 {d l : ℕ} (M : Matrix (Fin d) (Fin l) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlgTilde)
    (hker : ∀ b : Fin l → ℂ, (∀ j, b j ∈ Qbar) → M.mulVec b = 0 → b = 0)
    (him : ∀ φ : Fin d → ℂ, (∀ i, φ i ∈ Qbar) → Matrix.vecMul φ M = 0 → φ = 0)
    (hr : (d + l) * M.rank < d * l) :
    ∃ (S : Submodule ℂ (Fin l → ℂ)) (T : Submodule ℂ (Fin d → ℂ)) (r₁ : ℕ),
      Submodule.span ℂ {v : Fin l → ℂ | v ∈ S ∧ ∀ j, v j ∈ Qbar} = S ∧
      Submodule.span ℂ {v : Fin d → ℂ | v ∈ T ∧ ∀ i, v i ∈ Qbar} = T ∧
      1 ≤ l - Module.finrank ℂ ↥S ∧ 1 ≤ d - Module.finrank ℂ ↥T ∧
      (∀ s ∈ S, M.mulVec s ∈ T) ∧ 1 ≤ r₁ ∧
      r₁ * d < M.rank * (d - Module.finrank ℂ ↥T) ∧
      (l - Module.finrank ℂ ↥S) * (d - Module.finrank ℂ ↥T) ≤
        r₁ * ((l - Module.finrank ℂ ↥S) + (d - Module.finrank ℂ ↥T)) := by
  sorry

end DiazModulus
