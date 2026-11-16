-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_7
-- name    : BorderDiffEq.Supplement.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:58:28.696194+00:00
-- url     : https://prove2.me/theorems/688fa7df-525d-4325-a290-728cc213c96c
-- title:
--   Theorem 2.7 — deterministic non-adaptive reconstruction of border $\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)$ as depth-6 formulas
-- statement:
--   There is a deterministic, non-adaptive black-box reconstruction algorithm that, given integers $n,k,\delta,s$ with $n\le s$ and black-box access to an $n$-variate polynomial $f\in\overline{\Sigma^{[k]}\wedge\Sigma\Pi^{[\delta]}(s)}$ over a field of characteristic zero, outputs a depth-6 formula that computes $f$. The number of queries, the number of field operations and the size of the output formula are at most $s^{O(k^3\delta)}$.
--
--   Precisely: there are an absolute $C$ and a computable function $g$ (one algorithm for all parameters) such that for all $n,k,\delta,s$ with $n\le s$, $g(n,k,\delta,s)$ is the code of a list $Q\subseteq\mathbb Q^n$ of at most $(s+1)^{Ck^3\delta}$ query points and an algebraic program $A$ such that, for every field $F$ of characteristic zero and every $f$ in the border class, running $A$ on the values $(f(q))_{q\in Q}$ performs at most $(s+1)^{Ck^3\delta}$ operations (rational constants, $+,-,\times,\div$, zero tests) and outputs a formula over $F$ of depth at most $6$ and size at most $(s+1)^{Ck^3\delta}$ that computes $f$.
--
--   The algorithm runs in polynomial time for constant $k$ and $\delta$; it is improper (it outputs the depth-6 formula of Theorem 2.4, not a sum of powers) and applies to every polynomial of the border, not only to exact sums of powers.
--
--   **Formalization Note** The program model is `AlgProg`; the queries depend only on $(n,k,\delta,s)$, which makes the algorithm non-adaptive. Uniformity is Mathlib's `Computable` for the map $(n,k,\delta,s)\mapsto$ (prefix code of $Q$, then `AlgProg.code` of $A$).
--
--   Differences from the source:
--   - reading: "deterministic, non-adaptive blackbox reconstruction algorithm" counting field operations → a computable map from $(n,k,\delta,s)$ to a list of rational query points and an algebraic program (`AlgProg`) whose operations on the path taken are counted; reason: the paper counts field operations (p.61); computability of the map is the algorithm's uniformity, queries fixed in advance by the parameters are non-adaptivity, and determinism is the decision-tree form
--   - generalization: an algorithm over the fixed field $F$ → the same queries and program for every field of characteristic zero; reason: one algorithm for all $F$ specializes to each $F$
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - generalization: $\mathrm{size}(P)$ of a sum of monomials (undefined in the paper) → `spSize P` $=\sum_{m\in\mathrm{supp}P}(1+\#\mathrm{vars}(m))$; reason: at most the usual gate-and-wire count of the sum-of-monomials representation, so the size-bounded class contains the paper's for any standard size
--   - generalization: sums of $k$ terms → sums of at most $k$ terms; reason: padding with zero terms costs size, so the at-most-$k$ class can be larger; it contains the paper's class
--   - encoding: $s^{O(k^3\delta)}$ → $(s+1)^{Ck^3\delta}$, one absolute $C$; reason: reading of $O(\cdot)$; avoids a degenerate claim at $s\le1$
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.7, p.9; Algorithms 1 and 2, §8.1, pp.57–59; proof §8.2, pp.59–62

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_InBorderSumPowSP
import Definitions.Def_BorderDiffEq_Supplement_Formula
import Definitions.Def_BorderDiffEq_Supplement_AlgProg

namespace BorderDiffEq.Supplement

/-- **Theorem 2.7 (reconstruction for borders of sums of powers of low-degree polynomials)**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.7, p.9; Algorithms 1–2, §8.1, pp.57–59; proof §8.2, pp.59–62). There is a
deterministic, non-adaptive blackbox reconstruction algorithm that, given integers `n, k, δ, s` with
`n ≤ s` and blackbox access to an `n`-variate polynomial `f ∈ cl(Σ^{[k]} ∧ ΣΠ^{[δ]}(s))`, outputs a
depth-6 formula that computes `f`. The number of queries, the number of field operations and the
size of the output formula are at most `s^{O(k³δ)}`.

**Formalization Note.** For given `(n, k, δ, s)` the algorithm produces a list `Q` of query points
in `ℚⁿ` (non-adaptive: it depends only on the parameters) and an algebraic program `A` (`AlgProg`)
that receives the values `f(q)`, `q ∈ Q`, performs counted field operations (rational constants,
`+, −, ×, ÷`, zero tests) and outputs a formula over `F`. One algorithm serves all parameters:
`(n, k, δ, s) ↦ (Q, A)` is a computable function `g` (Mathlib's `Computable`), whose output is the
prefix code of `Q` (its length, then the codes `Encodable.encode` of the coordinates of each point)
followed by `AlgProg.code` of `A`. The same `Q` and `A` work over every field of characteristic
zero. `s^{O(k³δ)}` is `(s + 1)^{C·k³δ}`, one absolute `C`, bounding the number of queries, the
operations on the path taken, and the output size. -/
theorem theorem_2_7 : ∃ C : ℕ, ∃ g : ℕ × ℕ × ℕ × ℕ → List ℕ, Computable g ∧
    ∀ n k δ s : ℕ, n ≤ s →
    ∃ (Q : List (Fin n → ℚ)) (A : AlgProg (Fin n)),
      g (n, k, δ, s) =
        (Q.length :: Q.flatMap fun q => List.ofFn fun i => Encodable.encode (q i)) ++
          A.code Fin.val ∧
      Q.length ≤ (s + 1) ^ (C * k ^ 3 * δ) ∧
      ∀ (F : Type) [Field F] [CharZero F] (f : MvPolynomial (Fin n) F),
        InBorderSumPowSP F n k δ s f →
        (A.run (Q.map fun q => MvPolynomial.eval (fun i => (q i : F)) f)).2 ≤
            (s + 1) ^ (C * k ^ 3 * δ) ∧
          (A.run (Q.map fun q => MvPolynomial.eval (fun i => (q i : F)) f)).1.depth ≤ 6 ∧
          (A.run (Q.map fun q => MvPolynomial.eval (fun i => (q i : F)) f)).1.size ≤
            (s + 1) ^ (C * k ^ 3 * δ) ∧
          (A.run (Q.map fun q => MvPolynomial.eval (fun i => (q i : F)) f)).1.eval = f := by sorry

end BorderDiffEq.Supplement
