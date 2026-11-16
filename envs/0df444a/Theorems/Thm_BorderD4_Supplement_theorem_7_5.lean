-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_7_5
-- name    : BorderD4.Supplement.theorem_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:04:45.600492+00:00
-- url     : https://prove2.me/theorems/f7647bbc-82e4-44e0-b9cc-6be35ff4a422
-- title:
--   Theorem 7.5 (with Theorem 1.3) — no $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit computes $P_{k+1,n}$ for $n>(2k+\delta)\delta^{2k}+\delta^k$
-- statement:
--   Let $F$ be a field of characteristic $0$, $k,\delta\ge1$, and suppose
--   $$n>(2k+\delta)\delta^{2k}+\delta^k.$$
--   Then $P_{k+1,n}$ cannot be computed by any $\Sigma^{[k]}\Pi\Sigma\Pi^{[\delta]}$ circuit, regardless of its size.
--
--   This is the paper's exact impossibility result. Since $2(k+\delta)\delta^{2k}\ge(2k+\delta)\delta^{2k}+\delta^k$, it contains Theorem 1.3. Together with the $O(kn)$-size $\Sigma^{[k+1]}\Pi\Sigma$ circuit for $P_{k+1,n}$, it shows that top fan-in $k+1$ with bottom fan-in $1$ is strictly stronger than top fan-in $k$ with any constant bottom fan-in.
--
--   **Formalization Note** Circuits are the published `BorderD4.SPSP`, of any size.
--
--   Differences from the source:
--   - generalization: Theorem 7.5 under the standing assumption of §7 (p.77): F algebraically closed → every field F of characteristic 0; reason: Theorem 1.3 (p.5) states the result over any field of characteristic 0, by the transfer to the algebraic closure (§2, p.26); the algebraically closed case is a special case
--   - encoding: a Σ^[k]ΠΣΠ^[δ] circuit ∑_{i=1}^k T_i → the published `BorderD4.SPSP` with at most k product gates, T_i = C.gate i (the product gate times its output scalar), of any size; reason: the base mission's circuit model; a scalar does not change divisibility or homogeneity, and fewer than k gates is padding by zero gates
--   - encoding: variables x_1, …, x_N with blocks of n consecutive variables → variables Fin (k+1) × Fin n (the published `BorderD4.sumProduct`); reason: renaming of variables; the polynomial is the page's
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.5, p.82; Theorem 1.3, p.5; §2, p.26

import Mathlib
import Definitions.Def_BorderD4_sumProduct
import Definitions.Def_BorderD4_SPSP
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 7.5 (with Theorem 1.3): exact impossibility.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 7.5, p.82; Theorem 1.3, p.5 ("Our results hold over any field of characteristic 0"); the transfer to the algebraic closure, §2, p.26.

Let `F` be a field of characteristic `0`, `k, δ ≥ 1` and `n > (2k + δ)δ^{2k} + δ^k`. Then no `Σ^[k]ΠΣΠ^[δ]` circuit,
of any size, computes `P_{k+1,n}`.

**Formalization Note** Circuits are the published `BorderD4.SPSP` (any size, any numbers of middle and bottom gates,
any multiplicities). §7 states Theorem 7.5 over an algebraically closed field; the statement here is over every field
of characteristic `0`, as Theorem 1.3 claims. Since `2(k + δ)δ^{2k} ≥ (2k + δ)δ^{2k} + δ^k`, it contains Theorem 1.3. -/
theorem theorem_7_5 {F : Type*} [Field F] [CharZero F] (k δ n : ℕ) (hk : 1 ≤ k) (hδ : 1 ≤ δ)
    (hn : (2 * k + δ) * δ ^ (2 * k) + δ ^ k < n) :
    ∀ C : SPSP F (Fin (k + 1) × Fin n) k δ, C.eval ≠ sumProduct F k n := by sorry

end BorderD4.Supplement
