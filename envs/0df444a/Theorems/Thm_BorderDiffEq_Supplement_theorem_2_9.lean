-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_9
-- name    : BorderDiffEq.Supplement.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:58:59.652198+00:00
-- url     : https://prove2.me/theorems/b94ca3a0-2ebb-4272-b2cc-5e2e3c73fba9
-- title:
--   Theorem 2.9 — width $2^{\Omega(n/k^2)}$ lower bound for borders of sums of powers of common-order roABPs
-- statement:
--   Let $F$ be a field of characteristic zero, $n\ge2$, $k\ge1$, and $G_n=\prod_{1\le i<j\le n}(x_i+x_j)$. If $G_n^k\in\overline{\Sigma^{[k]}\wedge\mathrm{roABP}_\pi(w,R)}$ for some permutation $\pi$ of $[n]$ and some $R\ge0$, then
--   $$
--   w\ \ge\ 2^{\Omega(n/k^2)} .
--   $$
--
--   Here membership is the presentation (69): $\sum_{i=1}^{k}a_i(\epsilon)P_i^{e_i}=G_n^k+O(\epsilon)$ with $a_i\in F((\epsilon))$, positive integers $e_i$ with no bound, and every $P_i\in\mathrm{roABP}_\pi(w,R)$ over $F((\epsilon))$, the order $\pi$ being the same for all summands. Precisely: there is an absolute $c>0$ such that every such presentation has $2^{cn/k^2}\le w$, however large the exponents and the individual degree $R$.
--
--   $G_n^k$ has a formula of size $O(kn^2)$, so for constant $k$ approximating it in this model requires exponential width.
--
--   **Formalization Note** The class is `InBorderExt` with $\mathcal D_1=\mathrm{roABP}_\pi(w,R)$, $\mathcal D_2$ the constants and $e=\infty$. Theorem 9.6 (p.71) restates this theorem verbatim and is covered here.
--
--   Differences from the source:
--   - generalization: $\sum_{i=1}^kP_i^{e_i}$ (definition on p.7) → $\sum_{i}a_i(\epsilon)P_i^{e_i}$ with $a_i\in F((\epsilon))$, the presentation (69); reason: §9.2 states the theorem for (69); taking $a_i=1$ gives p.7's class, so the lower bound over (69) implies it
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - encoding: sums of $k$ terms → sums of at most $k$ terms; reason: every class used contains $0$ and $0^1=0$, so padding with zero terms gives the same class
--   - encoding: $\Omega(n/k^2)$ → $c\,n/k^2$ with one absolute $c>0$; reason: reading of $\Omega$
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.9, p.10; Theorem 9.6 and display (69), p.71; proof §9.2, pp.70–75

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_InBorderExt
import Definitions.Def_BorderDiffEq_Supplement_InRoABP
import Definitions.Def_BorderDiffEq_Supplement_Gpoly

namespace BorderDiffEq.Supplement

/-- **Theorem 2.9 (lower bounds for borders of sums of powers of roABPs)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.9,
p.10; restated as Theorem 9.6, p.71, with the presentation (69); proof §9.2, pp.70–75). Let `n ≥ 2`
and `k ≥ 1` be integers, and let `Gₙ(x) := ∏_{1≤i<j≤n} (xᵢ + xⱼ)`. If `Gₙ^k ∈ cl(Σ^{[k]} ∧ roABP_π(w, R))`
for some permutation `π` of `[n]` and some `R ≥ 0`, then `w ≥ 2^{Ω(n/k²)}`.

**Formalization Note.** The border is the presentation (69), p.71:
`∑_{i=1}^{k} aᵢ(ε) Pᵢ^{eᵢ} = Gₙ^k + O(ε)` with `aᵢ ∈ F((ε))`, exponents `eᵢ ≥ 1` unrestricted
(`e = ⊤`), and every `Pᵢ ∈ roABP_π(w, R)` over `F((ε))`, one order `π` for all summands. It is
`InBorderExt` with `qᵢ = aᵢ` constant. `Ω` is one absolute `c > 0`, chosen before the field and
every parameter. -/
theorem theorem_2_9 : ∃ c : ℝ, 0 < c ∧ ∀ (F : Type) [Field F] [CharZero F] (n k : ℕ)
    (π : Equiv.Perm (Fin n)) (w R : ℕ), 2 ≤ n → 1 ≤ k →
    InBorderExt F n k ⊤ (InRoABP (LaurentSeries F) n π w R)
      (fun q => ∃ a : LaurentSeries F, q = MvPolynomial.C a) (Gpoly F n ^ k) →
    (2 : ℝ) ^ (c * n / k ^ 2) ≤ w := by sorry

end BorderDiffEq.Supplement
