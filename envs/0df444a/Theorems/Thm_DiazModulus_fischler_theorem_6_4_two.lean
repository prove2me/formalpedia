-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_6_4_two
-- name    : DiazModulus.fischler_theorem_6_4_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:36.829062+00:00
-- url     : https://prove2.me/theorems/54747983-8fd8-49f9-9aba-c0259dc2a9ad
-- title:
--   Fischler 2001, Th. 6.4 (2): if m ≥ 2 and v ∈ ℂᵐ has vᵢvⱼ ∈ ℒ̃ for all i, j, then v lies in a 2-dimensional subspace of ℂᵐ spanned by two vectors of Q̄ᵐ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $m \ge 2$ and $v \in \mathbb C^m$, and suppose that $v_i v_j \in \widetilde{\mathcal L}$ for all $i, j \in \{1, \dots, m\}$ (the coordinates of $v \otimes v$ in the basis $e_i \otimes e_j$). Then there are $w_1, w_2 \in \mathbb C^m$ with algebraic coordinates, linearly independent over $\mathbb C$, such that $v$ lies in the $\mathbb C$-span of $w_1$ and $w_2$. So $F = \mathbb C w_1 + \mathbb C w_2$ is a subspace of $\mathbb C^m$ defined over $\overline{\mathbb Q}$, of dimension $2$, which contains $v$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.4, part 2 (p. 185), complex case, in the coordinates of the basis eᵢ ⊗ eⱼ, which is defined over Q̄; a subspace defined over Q̄ is one spanned by vectors with algebraic coordinates (p. 170). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The hypothesis m ≥ 2 is printed and needed. Proved from DiazModulus.fischler_power_span_finrank, DiazModulus.fischler_rational_hull and DiazModulus.qbar_linearIndependent_complex. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_6_4_two {m : ℕ} (hm : 2 ≤ m) (v : Fin m → ℂ)
    (hv : ∀ I : Fin 2 → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ w : Fin 2 → Fin m → ℂ, (∀ a i, w a i ∈ Qbar) ∧ LinearIndependent ℂ w ∧
      v ∈ Submodule.span ℂ (Set.range w) := by
  sorry

end DiazModulus
