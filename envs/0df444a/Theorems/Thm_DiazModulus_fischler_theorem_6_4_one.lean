-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_6_4_one
-- name    : DiazModulus.fischler_theorem_6_4_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:27.902801+00:00
-- url     : https://prove2.me/theorems/8c8620d4-3332-4eea-9be5-8681f7b938a2
-- title:
--   Fischler 2001, Th. 6.4 (1): if k ≥ 3 and v ⊗ ⋯ ⊗ v (k factors) has its coordinates in ℒ̃, then v ⊗ ⋯ ⊗ v = a v′ ⊗ ⋯ ⊗ v′ with a ∈ ℒ̃ and v′ ∈ Q̄ᵐ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $v \in \mathbb C^m$ and a map $I : \{1, \dots, k\} \to \{1, \dots, m\}$ write $v_I = v_{I(1)} v_{I(2)} \cdots v_{I(k)}$; these are the coordinates of $v \otimes \cdots \otimes v$ ($k$ factors) in the basis $e_{I(1)} \otimes \cdots \otimes e_{I(k)}$ of $(\mathbb C^m)^{\otimes k}$, which is defined over $\overline{\mathbb Q}$.
--
--   Let $k \ge 3$ and $v \in \mathbb C^m$, and suppose that $v_I \in \widetilde{\mathcal L}$ for every map $I : \{1, \dots, k\} \to \{1, \dots, m\}$. Then there are $a \in \widetilde{\mathcal L}$ and $v' \in \mathbb C^m$ with algebraic coordinates such that $v_I = a\,v'_I$ for every $I$, that is, $v \otimes \cdots \otimes v = a\, v' \otimes \cdots \otimes v'$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.4, part 1 (p. 185), complex case, for any m (printed: m ≥ 2), in the coordinates of the basis e_I(1) ⊗ ⋯ ⊗ e_I(k), which is defined over Q̄ (p. 170). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The printed proof (pp. 185–186) stops at n ≤ 1 and leaves implicit why a lies in ℒ̃; here a = c₀ᵏ is a Q̄-multiple of the coordinate vⱼᵏ. Proved from DiazModulus.fischler_power_span_finrank and DiazModulus.fischler_rational_hull. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_6_4_one {m k : ℕ} (hk : 3 ≤ k) (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ a ∈ LogAlgTilde, ∃ v' : Fin m → ℂ, (∀ i, v' i ∈ Qbar) ∧
      ∀ I : Fin k → Fin m, ∏ t, v (I t) = a * ∏ t, v' (I t) := by
  sorry

end DiazModulus
