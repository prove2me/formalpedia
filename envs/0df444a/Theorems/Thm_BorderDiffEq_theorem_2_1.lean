-- Prove2me | Theorems.Thm_BorderDiffEq_theorem_2_1
-- name    : BorderDiffEq.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:37.020044+00:00
-- url     : https://prove2.me/theorems/df2824bf-bed4-4f1c-9b4e-04df2218677c
-- title:
--   Theorem 2.1 — every $f\in\overline{\Sigma^{[k]}\Pi\Sigma(s)}$ has an ABP of size $s^{O(k^2)}$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $F$ be a field of characteristic zero, let $k,s\ge1$ be integers, and let $f\in F[x_1,\dots,x_n]$ lie in the border of depth-3 circuits of top fan-in $k$ and size $s$:
--   $$
--   f\in\overline{\Sigma^{[k]}\Pi\Sigma(s)} .
--   $$
--   Then $f$ is computed by an algebraic branching program over $F$ with affine labels and at most
--   $$
--   (s+1)^{C k^2}
--   $$
--   vertices.
--
--   This is the paper's debordering theorem: polynomials that are merely approximated by small depth-3 circuits of top fan-in $k$ are computed exactly by ABPs of size $s^{O(k^2)}$, quasipolynomial for every $k=(\log s)^{O(1)}$; the previous bound was $s^{O(k\cdot7^k)}$.
--
--   **Formalization Note** The border allows constants in $F((\varepsilon))$ and requires the circuit to compute $f+\varepsilon S$ with $S\in F[[\varepsilon]][x]$. The circuit size counts every affine factor with multiplicity together with the variables it uses, so it bounds the formal degree. The ABP size is its number of vertices.
--
--   Differences from the source:
--   - reading: ABP of size $s^{O(k^2)}$ → at most $(s+1)^{Ck^2}$ vertices with one absolute $C$ before the field and all parameters; reason: for $s\ge2$ this is the same class of bounds as $s^{C'k^2}$; at $s=1$ the literal $s^{O(k^2)}=1$ would claim a one-vertex ABP
--   - generalization: circuit constants in $F(\varepsilon)$, $f+\varepsilon g$ with $g\in F[\varepsilon][x]$ → constants in $F((\varepsilon))$, $f+\varepsilon S$ with $S\in F[[\varepsilon]][x]$; reason: $F(\varepsilon)\subset F((\varepsilon))$ and $F[\varepsilon]\subset F[[\varepsilon]]$, so the source's border is contained in the Lean one
--   - generalization: circuit size (not defined in the paper) → $\sum_i(1+\sum_j(1+|\mathrm{supp}\,\ell_{ij}|))$, factors with multiplicity; reason: this is at most the number of gates plus wires, so each size class is at least as large as the source's; it still bounds the formal degree, the top fan-in and the number of variables, which is all the proof uses
--   - generalization: top fan-in $k$ → top fan-in at most $k$; reason: a circuit with exactly $k$ product gates has at most $k$, so the source's border class is contained in the Lean one
--   - encoding: variables $x_1,\dots,x_n$ → variables `Fin n`; reason: relabelling of the variables
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.1, p.7 (proof §6.1, pp.44–45)

import Mathlib
import Definitions.Def_BorderDiffEq_InBorderSPS
import Definitions.Def_BorderDiffEq_ABP

namespace BorderDiffEq

/-- **Theorem 2.1 (debordering depth-3 circuits)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Theorem 2.1, p.7; proof §6.1, pp.44–45). Let `k, s ≥ 1` be integers and let
`f ∈ cl(Σ^{[k]}ΠΣ(s))`. Then `f` can be computed by an ABP of size `s^{O(k²)}`.

**Formalization Note.** `s^{O(k²)}` is read as `(s + 1)^{C·k²}` with one absolute constant `C`
quantified before the field and every parameter (for `s ≥ 2` this is the same class of bounds as
`s^{C'k²}`; at `s = 1` it avoids claiming a one-vertex ABP). `F` is any field of characteristic
zero, variables are `Fin n`. The border (`InBorderSPS`) has constants in `F((ε))` and `f + ε·S`
with `S ∈ F[[ε]][x]`, which covers the paper's `F(ε)` constants and `g ∈ F[ε][x]`; the circuit size
counts every factor with multiplicity (`SPS.size`). The ABP is over `F`, with affine labels, and its
size is its number of vertices. -/
theorem theorem_2_1 : ∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (n k s : ℕ)
    (f : MvPolynomial (Fin n) F), 1 ≤ k → 1 ≤ s → InBorderSPS F n k s f →
    ∃ A : ABP F (Fin n), A.eval = f ∧ A.size ≤ (s + 1) ^ (C * k ^ 2) := by sorry

end BorderDiffEq
