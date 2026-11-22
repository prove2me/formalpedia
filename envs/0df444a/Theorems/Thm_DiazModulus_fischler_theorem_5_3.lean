-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_5_3
-- name    : DiazModulus.fischler_theorem_5_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-21T08:08:06.510556+00:00
-- url     : https://prove2.me/theorems/0da189c7-9ca1-4b6a-bf9b-d3068786d652
-- title:
--   Fischler 2001, Th. 5.3, with a vector hyperplane: if m, k ≥ 2, (k, m) ≠ (2, 2) and v ⊗ ⋯ ⊗ v (k factors) has its coordinates in ℒ̃, it lies in a vector hyperplane defined over Q̄
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $v \in \mathbb C^m$ and a map $I : \{1, \dots, k\} \to \{1, \dots, m\}$ write $v_I = v_{I(1)} v_{I(2)} \cdots v_{I(k)}$; these are the coordinates of $v \otimes \cdots \otimes v$ ($k$ factors) in the basis $e_{I(1)} \otimes \cdots \otimes e_{I(k)}$ of $(\mathbb C^m)^{\otimes k}$, which is defined over $\overline{\mathbb Q}$.
--
--   Let $m \ge 2$ and $k \ge 2$ with $(k, m) \neq (2, 2)$, let $v \in \mathbb C^m$, and suppose that $v_I \in \widetilde{\mathcal L}$ for every map $I : \{1, \dots, k\} \to \{1, \dots, m\}$. Then there is a family $(\psi_I)_I$ of algebraic numbers, indexed by these maps and not all zero, such that
--   $$\sum_I \psi_I v_I = 0.$$
--   So $v \otimes \cdots \otimes v$ lies in the vector hyperplane $\sum_I \psi_I x_I = 0$ of $(\mathbb C^m)^{\otimes k}$, which is defined over $\overline{\mathbb Q}$: Fischler's Conjecture 2 for the set $\mathcal T(k, m)$ of tensors $v \otimes \cdots \otimes v$, with a hyperplane through $0$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 5.3 (p. 180), in the setting of §5.1 (m ≥ 2, k ≥ 2, p. 178), with Conjecture 2 (p. 168) in the coordinates of the basis e_I(1) ⊗ ⋯ ⊗ e_I(k), which is defined over Q̄ (p. 170). The conclusion is slightly stronger than printed: the hyperplane is a vector hyperplane, where Conjecture 2 asks for an affine one; Fischler notes that his method gives vector hyperplanes (p. 169). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The printed proof goes through the orbit results of §4 and is sketched (p. 178); Fischler points to Th. 6.4 for a more precise result (p. 180). The proof here uses only the bound n ≤ 2, and n ≤ 1 for k ≥ 3, on the dimension n of the Q̄-span of v₁, …, vₘ, the common core of the proofs of Th. 6.2 and Th. 6.4: it gives n < m, so the vᵢ are linearly dependent over Q̄, and a relation Σ βᵢvᵢ = 0 gives ψ. Neither Th. 6.4 nor the rational hull of v is used. Proved from DiazModulus.fischler_power_span_finrank. Formal proof: Diaz modulus mission, 20 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_5_3 {m k : ℕ} (hm : 2 ≤ m) (hk : 2 ≤ k) (hkm : (k, m) ≠ (2, 2))
    (v : Fin m → ℂ) (hv : ∀ I : Fin k → Fin m, ∏ t, v (I t) ∈ LogAlgTilde) :
    ∃ ψ : (Fin k → Fin m) → ℂ, (∀ I, ψ I ∈ Qbar) ∧ ψ ≠ 0 ∧
      ∑ I, ψ I * ∏ t, v (I t) = 0 := by
  sorry

end DiazModulus
