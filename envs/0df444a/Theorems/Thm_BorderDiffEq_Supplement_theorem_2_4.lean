-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_4
-- name    : BorderDiffEq.Supplement.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:56:13.303307+00:00
-- url     : https://prove2.me/theorems/2ce6c71a-4f3b-4009-ad41-132713f15269
-- title:
--   Theorem 2.4 — border $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$ has depth-6 formulas of size $s^{O(k^3\delta)}$
-- statement:
--   Let $F$ be a field of characteristic zero and $k,\delta,s\ge1$. If $f\in\overline{\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)}$, then $f$ is computed by a formula of depth six over $F$ of size $s^{O(k^3\delta)}$.
--
--   Precisely: there is an absolute $C$ such that every such $f\in F[x_1,\dots,x_n]$ (any $n$) is computed by a formula over $F$ with constants in $F$, of depth at most $6$ and size at most
--   $$
--   (s+1)^{C k^3\delta}.
--   $$
--
--   For constant $k$ and $\delta$ the formulas have polynomial size; this answers whether the border of $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}$ lies in VBP for constant $k,\delta$. It is the case $q_i=1$ of Theorem 6.2.
--
--   Differences from the source:
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - generalization: $\mathrm{size}(P)$ of a sum of monomials (undefined in the paper) → `spSize P` $=\sum_{m\in\mathrm{supp}P}(1+\#\mathrm{vars}(m))$; reason: at most the usual gate-and-wire count of the sum-of-monomials representation, so the size-bounded class contains the paper's for any standard size
--   - generalization: sums of $k$ terms → sums of at most $k$ terms; reason: padding with zero terms costs size, so the at-most-$k$ class can be larger; it contains the paper's class
--   - encoding: $s^{O(k^3\delta)}$ → $(s+1)^{Ck^3\delta}$ with one absolute $C$; reason: reading of $O(\cdot)$; $s+1\le s^2$ for $s\ge2$, so it is the same class of bounds, and it avoids a degenerate claim at $s=1$
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.4, p.8; Theorem 6.2 and its proof, pp.48–50

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_InBorderSumPowSP
import Definitions.Def_BorderDiffEq_Supplement_Formula

namespace BorderDiffEq.Supplement

/-- **Theorem 2.4 (debordering sums of powers of polynomials of bounded degree)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem
2.4, p.8; a special case of Theorem 6.2, proved in §6.2). Let `k, δ, s ≥ 1` be integers, and let
`f ∈ cl(Σ^{[k]} ∧ ΣΠ^{[δ]}(s))`. Then `f` is computed by a formula of depth six and size
`s^{O(k³δ)}`.

**Formalization Note.** `s^{O(k³δ)}` is `(s + 1)^{C·k³δ}` with one absolute `C` chosen before the
field and every parameter. The formula (`Formula`) is over `F` (constants in `F`, no `ε`, no
division), of depth at most `6`, and computes `f` exactly. `F` is any field of characteristic
zero, the variables are `Fin n`, and `n` is not bounded. -/
theorem theorem_2_4 : ∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k δ s : ℕ)
    (f : MvPolynomial (Fin n) F), 1 ≤ k → 1 ≤ δ → 1 ≤ s → InBorderSumPowSP F n k δ s f →
    ∃ φ : Formula F (Fin n), φ.depth ≤ 6 ∧ φ.size ≤ (s + 1) ^ (C * k ^ 3 * δ) ∧ φ.eval = f := by sorry

end BorderDiffEq.Supplement
