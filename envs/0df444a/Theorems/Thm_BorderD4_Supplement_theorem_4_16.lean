-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_4_16
-- name    : BorderD4.Supplement.theorem_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:02:42.21701+00:00
-- url     : https://prove2.me/theorems/e0c05750-7d32-4092-a488-cdda0b275e31
-- title:
--   Theorem 4.16 — border impossibility under a constant-freeness assumption
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$, $k,\delta\ge 1$ and $n>k\delta^k$. Then:
--
--   1. $P_{k+1,n}$ cannot be approximately computed by a circuit $\sum_{i=1}^k T_i$ over $F((\varepsilon))$ in which each $T_i$ is either a constant or divisible by a constant-free polynomial $q_i\in F((\varepsilon))[x]$ of degree at most $\delta$;
--   2. in particular, $P_{k+1,n}$ cannot be approximately computed by a homogeneous $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit over $F((\varepsilon))$.
--
--   Here a circuit over $F((\varepsilon))$ approximately computes $P_{k+1,n}$ if it computes $P_{k+1,n}+\varepsilon S$ for some $S\in F[[\varepsilon]][x]$ (Definition 2.12). Without the constant-freeness assumption the statement fails for $k\ge 2$, since $P_{k+1,n}$ has border $\Sigma^{[2]}\Pi\Sigma$ circuits.
--
--   **Formalization Note** Approximate computation is the published `BorderD4.BorderComputes`; circuits are the published `BorderD4.SPSP` over $F((\varepsilon))$, of any size.
--
--   Differences from the source:
--   - encoding: a Σ^[k]ΠΣΠ^[δ] circuit ∑_{i=1}^k T_i → the published `BorderD4.SPSP` with at most k product gates, T_i = C.gate i (the product gate times its output scalar), of any size; reason: the base mission's circuit model; a scalar does not change divisibility or homogeneity, and fewer than k gates is padding by zero gates
--   - encoding: variables x_1, …, x_N with blocks of n consecutive variables → variables Fin (k+1) × Fin n (the published `BorderD4.sumProduct`); reason: renaming of variables; the polynomial is the page's
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 4.16, p.44; standing assumptions p.3 and §4, p.38; Definition 2.12, p.33

import Mathlib
import Definitions.Def_BorderD4_sumProduct
import Definitions.Def_BorderD4_SPSP
import Definitions.Def_BorderD4_BorderComputes
import Definitions.Def_BorderD4_Supplement_IsHomogeneousCircuit
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 4.16: impossibility under a constant-freeness assumption in the border setting.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 4.16, p.44; standing assumptions p.3 (characteristic `0`) and §4, p.38 (`F` algebraically closed); Definition 2.12, p.33.

Let `k, δ ≥ 1` and `n > kδ^k`. Then
1. no circuit `∑_{i=1}^k T_i` over `F((ε))` in which each `T_i` is a constant or is divisible by a constant-free
   `q_i ∈ F((ε))[x]` of degree at most `δ` approximately computes `P_{k+1,n}`;
2. no homogeneous `Σ^[k]ΠΣΠ^[δ]` circuit over `F((ε))` approximately computes `P_{k+1,n}`.

**Formalization Note** "Approximately computes" is the published `BorderD4.BorderComputes` (Definition 2.12: the
circuit computes `P_{k+1,n} + εS` with `S ∈ F[[ε]][x]`). Circuits are the published `BorderD4.SPSP` over
`LaurentSeries F`, of any size; `T_i = C.gate i`; constants are constant polynomials `C c`, `c ∈ F((ε))`
(possibly `0`); "constant-free" means `q(0) = 0`; the degree is the total degree in `x`. -/
theorem theorem_4_16 {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (k δ n : ℕ) (hk : 1 ≤ k) (hδ : 1 ≤ δ)
    (hn : k * δ ^ k < n) :
    (∀ C : SPSP (LaurentSeries F) (Fin (k + 1) × Fin n) k δ,
      (∀ i, (∃ c : LaurentSeries F, C.gate i = MvPolynomial.C c) ∨
        ∃ q : MvPolynomial (Fin (k + 1) × Fin n) (LaurentSeries F),
          constantCoeff q = 0 ∧ q.totalDegree ≤ δ ∧ q ∣ C.gate i) →
      ¬ BorderComputes C (sumProduct F k n)) ∧
    (∀ C : SPSP (LaurentSeries F) (Fin (k + 1) × Fin n) k δ, IsHomogeneousCircuit C →
      ¬ BorderComputes C (sumProduct F k n)) := by sorry

end BorderD4.Supplement
