-- Prove2me | Theorems.Thm_DiazModulus_fischler_power_span_finrank
-- name    : DiazModulus.fischler_power_span_finrank
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:19.036113+00:00
-- url     : https://prove2.me/theorems/fdaa3cb3-61bf-479c-9c18-2fbc9cb54f02
-- title:
--   If k ≥ 2 and every product of k coordinates of v ∈ ℂᵐ lies in ℒ̃, then v₁, …, vₘ span a Q̄-space of dimension at most 2, and at most 1 if k ≥ 3
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $k \ge 2$ and $v \in \mathbb C^m$, and suppose that $v_{I(1)} v_{I(2)} \cdots v_{I(k)} \in \widetilde{\mathcal L}$ for every map $I : \{1, \dots, k\} \to \{1, \dots, m\}$. Then the $\overline{\mathbb Q}$-span of $v_1, \dots, v_m$ has dimension at most $2$ over $\overline{\mathbb Q}$, and at most $1$ if $k \ge 3$.
-- source:
--   Step of the proofs of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.2 and Th. 6.4 (pp. 184–186): their common core, n ≤ 2, and n ≤ 1 for k ≥ 3, with n the dimension of the Q̄-span of the coefficients. The printed proofs apply Th. 2.3 to a symmetric n × n matrix and, for k ≥ 3, Lemma 6.1; here both steps apply Roy's strong six exponentials theorem in product form (DiazModulus.strong_six_exponentials_unconditional) to a 2 × 3 corner, and Lemma 6.1 is not used. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_power_span_finrank {m k : ℕ} (hk : 2 ≤ k) (v : Fin m → ℂ)
    (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ≤ 2 ∧
      (3 ≤ k → Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ≤ 1) := by
  sorry

end DiazModulus
