-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_3
-- name    : BorderDiffEq.Supplement.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:55:25.873001+00:00
-- url     : https://prove2.me/theorems/6a456d38-18c7-435d-85d8-1473a6a7d4a8
-- title:
--   Theorem 2.3 — border top fan-in hierarchy: $P_{k+1,d}$ needs size $2^{\Omega(d/k^2)}$ with $k$ products
-- statement:
--   Let $F$ be a field of characteristic zero and $d>k\ge1$. The polynomial $P_{k+1,d}=\sum_{i=1}^{k+1}\prod_{j=1}^{d}x_{i,j}$ has $N=(k+1)d$ variables and degree $d$, and it is computed by a depth-3 circuit of top fan-in $k+1$ and size $O(N)$. However, if $P_{k+1,d}\in\overline{\Sigma^{[k]}\Pi\Sigma(s)}$, then
--   $$
--   s\ \ge\ 2^{\Omega(d/k^2)} .
--   $$
--
--   Precisely: there are an absolute $C$ and an absolute $c>0$ such that (1) $P_{k+1,d}$ uses all $N$ variables, has total degree $d$, and equals the polynomial of a depth-3 circuit over $F$ with exactly $k+1$ product gates and size at most $CN$; and (2) whenever $P_{k+1,d}$ lies in the border of depth-3 circuits with at most $k$ product gates and size at most $s$, then $2^{c\,d/k^2}\le s$.
--
--   This improves the exponent's dependence on $k$ from $\exp(k)$ to $k^2$ and separates top fan-in $k+1$ from top fan-in $k$ in the border.
--
--   **Formalization Note** The circuit and size are the published `BorderDiffEq.SPS` and `SPS.size`; the border is the published `BorderDiffEq.InBorderSPS`. Theorem 9.4 (p.68) restates the lower bound and is covered here.
--
--   Differences from the source:
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - generalization: circuit size (left undefined by the paper) → the published `SPS.size` (each factor counts one plus the variables it uses); reason: it is at most the usual count of gates and wires, so the lower bound for it implies the bound for any standard size
--   - encoding: $O(N)$ and $\Omega(d/k^2)$ → $C\cdot N$ and $c\cdot d/k^2$ with absolute $C$ and $c>0$; reason: reading of $O$/$\Omega$
--   - encoding: variables $x_{i,j}$ → `Fin ((k+1)*d)` via `finProdFinEquiv`; reason: Lean convention; same polynomial
--   - encoding: "has $N$ variables" → `vars = univ`; reason: every one of the $N$ variables occurs
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.3, p.7; Theorem 9.4, p.68; proof §9.1, pp.62–70

import Mathlib
import Definitions.Def_BorderDiffEq_InBorderSPS
import Definitions.Def_BorderDiffEq_Supplement_hardP

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **Theorem 2.3 (improved border top fan-in hierarchy)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.3, p.7; lower bound
restated as Theorem 9.4, p.68; proof §9.1, pp.62–70). Let `d > k ≥ 1` be integers. The polynomial
`P_{k+1,d}` has `N := (k+1)d` variables and degree `d`, and it is computed by a depth-3 circuit of
top fan-in `k + 1` and size `O(N)`. However, if `P_{k+1,d} ∈ cl(Σ^{[k]}ΠΣ(s))`, then
`s ≥ 2^{Ω(d/k²)}`.

**Formalization Note.** Both halves are stated. The circuit is a base `SPS` over `F` with exactly
`k + 1` product gates and `SPS.size ≤ C·N`; "has `N` variables" is `vars = univ` on `Fin N`. The
lower bound uses the published border `InBorderSPS` (constants in `F((ε))`, size `SPS.size`) with
one absolute `c > 0` for `Ω`: `2^{c·d/k²} ≤ s`. `F` is any field of characteristic zero. -/
theorem theorem_2_3 :
    (∃ C : ℕ, ∀ (F : Type) [Field F] [CharZero F] (k d : ℕ), 1 ≤ k → k < d →
      (hardP F k d).vars = Finset.univ ∧ (hardP F k d).totalDegree = d ∧
      ∃ Φ : SPS F (Fin ((k + 1) * d)), Φ.eval = hardP F k d ∧ Φ.topFanIn = k + 1 ∧
        Φ.size ≤ C * ((k + 1) * d)) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ (F : Type) [Field F] [CharZero F] (k d s : ℕ), 1 ≤ k → k < d →
      InBorderSPS F ((k + 1) * d) k s (hardP F k d) → (2 : ℝ) ^ (c * d / k ^ 2) ≤ s) := by sorry

end BorderDiffEq.Supplement
