-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_3_1
-- name    : BorderD4.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:02:07.124219+00:00
-- url     : https://prove2.me/theorems/57982d4e-b0de-48f5-a60a-2a8d08b7625a
-- title:
--   Theorem 3.1 — impossibility under a constant-freeness assumption
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$, $k,\delta\ge 1$ and $n>k\delta^k$. Then:
--
--   1. $P_{k+1,n}$ cannot be computed by a $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit $\sum_{i=1}^k T_i$ in which each $T_i$ is either a constant or divisible by a constant-free polynomial $q_i$ (that is, $q_i(0)=0$) of degree at most $\delta$;
--   2. in particular, $P_{k+1,n}$ cannot be computed by a homogeneous $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit.
--
--   This is the warm-up exact impossibility result: it holds for circuits of every size, and it rules out homogeneous depth-4 circuits with top fan-in $k$ for $P_{k+1,n}$.
--
--   **Formalization Note** Circuits are the published `BorderD4.SPSP`; $T_i$ is a product gate with its output scalar. Constants may be $0$.
--
--   Differences from the source:
--   - encoding: a Σ^[k]ΠΣΠ^[δ] circuit ∑_{i=1}^k T_i → the published `BorderD4.SPSP` with at most k product gates, T_i = C.gate i (the product gate times its output scalar), of any size; reason: the base mission's circuit model; a scalar does not change divisibility or homogeneity, and fewer than k gates is padding by zero gates
--   - encoding: variables x_1, …, x_N with blocks of n consecutive variables → variables Fin (k+1) × Fin n (the published `BorderD4.sumProduct`); reason: renaming of variables; the polynomial is the page's
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 3.1, p.37; standing assumptions p.3 and §3, p.37

import Mathlib
import Definitions.Def_BorderD4_sumProduct
import Definitions.Def_BorderD4_SPSP
import Definitions.Def_BorderD4_Supplement_IsHomogeneousCircuit
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 3.1: impossibility under a constant-freeness assumption.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 3.1, p.37; standing assumptions p.3 (characteristic `0`) and §3, p.37 (`F` algebraically closed).

Let `k, δ ≥ 1` and `n > kδ^k`. Then
1. no `Σ^[k]ΠΣΠ^[δ]` circuit `∑_{i=1}^k T_i` in which each `T_i` is a constant or is divisible by a constant-free
   polynomial `q_i` of degree at most `δ` computes `P_{k+1,n}`;
2. no homogeneous `Σ^[k]ΠΣΠ^[δ]` circuit computes `P_{k+1,n}`.

**Formalization Note** Circuits are the published `BorderD4.SPSP` (any size, any numbers of middle and bottom gates,
any multiplicities); `T_i` is the product gate with its output scalar, `C.gate i`. "Constant" means a constant
polynomial `C c` (possibly `0`); "constant-free" means `q(0) = 0`; the degree is the total degree. -/
theorem theorem_3_1 {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (k δ n : ℕ) (hk : 1 ≤ k) (hδ : 1 ≤ δ)
    (hn : k * δ ^ k < n) :
    (∀ C : SPSP F (Fin (k + 1) × Fin n) k δ,
      (∀ i, (∃ c : F, C.gate i = MvPolynomial.C c) ∨
        ∃ q : MvPolynomial (Fin (k + 1) × Fin n) F,
          constantCoeff q = 0 ∧ q.totalDegree ≤ δ ∧ q ∣ C.gate i) →
      C.eval ≠ sumProduct F k n) ∧
    (∀ C : SPSP F (Fin (k + 1) × Fin n) k δ, IsHomogeneousCircuit C → C.eval ≠ sumProduct F k n) := by sorry

end BorderD4.Supplement
