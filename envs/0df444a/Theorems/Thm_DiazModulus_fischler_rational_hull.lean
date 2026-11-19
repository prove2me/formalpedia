-- Prove2me | Theorems.Thm_DiazModulus_fischler_rational_hull
-- name    : DiazModulus.fischler_rational_hull
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:16.936212+00:00
-- url     : https://prove2.me/theorems/af5c721e-e373-40d2-a657-850d2069764e
-- title:
--   For v ∈ ℂᵐ: v = c₁w₁ + ⋯ + cₙwₙ with c Q̄-free, w₁, …, wₙ ∈ Q̄ᵐ Q̄-free, n = dim span_Q̄(v₁, …, vₘ), and each algebraic ψ with ψ · v = 0 vanishes on every wₐ
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   For $u, v \in \mathbb C^m$ write $u \cdot v = \sum_i u_i v_i$. Let $v \in \mathbb C^m$, and let $n$ be the dimension over $\overline{\mathbb Q}$ of the $\overline{\mathbb Q}$-span of $v_1, \dots, v_m$. Then there are $c_1, \dots, c_n \in \mathbb C$, linearly independent over $\overline{\mathbb Q}$, and vectors $w_1, \dots, w_n \in \mathbb C^m$ with algebraic coordinates, linearly independent over $\overline{\mathbb Q}$, such that
--   $$v = c_1 w_1 + \dots + c_n w_n,$$
--   and every $\psi \in \mathbb C^m$ with algebraic coordinates and $\psi \cdot v = 0$ satisfies $\psi \cdot w_a = 0$ for $a = 1, \dots, n$.
-- source:
--   Step of the proofs of S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.2 and Th. 6.4 (pp. 184–186): the ℂ-span of the wₐ is the smallest subspace of ℂᵐ defined over Q̄ that contains v (p. 185), given here by an explicit decomposition. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_rational_hull {m : ℕ} (v : Fin m → ℂ) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → Fin m → ℂ),
      n = Module.finrank (↥Qbar) ↥(Submodule.span (↥Qbar) (Set.range v)) ∧
      LinearIndependent (↥Qbar) c ∧ LinearIndependent (↥Qbar) w ∧ (∀ a i, w a i ∈ Qbar) ∧
      v = ∑ a, c a • w a ∧
      ∀ ψ : Fin m → ℂ, (∀ i, ψ i ∈ Qbar) → ψ ⬝ᵥ v = 0 → ∀ a, ψ ⬝ᵥ w a = 0 := by
  sorry

end DiazModulus
