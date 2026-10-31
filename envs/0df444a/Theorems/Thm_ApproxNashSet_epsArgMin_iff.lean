-- Prove2me | Theorems.Thm_ApproxNashSet_epsArgMin_iff
-- name    : ApproxNashSet.epsArgMin_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:46.843032+00:00
-- url     : https://prove2.me/theorems/5bb66841-1d09-450a-8ecd-beaff12d52aa
-- title:
--   Proof of Theorem 3.2 — ε-Pareto optimality for problem (3) in direction $\bar c_i$ is a unilateral ε-best response
-- statement:
--   Let $f_i$ be the costs of a shared-constraint game on $\mathbb X\subseteq\prod_jX_j$, fix a player $i$ and a real $\varepsilon$, and let $g_i(x)=(x_{-i},-x_{-i},f_i(x))$ be the objective of problem (3), ordered componentwise, with direction $\bar c_i=(0,\dots,0,1)$. Then a joint strategy $x^*$ is $\varepsilon$-Pareto optimal for (3) with respect to $\bar c_i$ if and only if
--   $$x^*\in\mathbb X\quad\text{and}\quad f_i(x^*)\le f_i(x_i,x^*_{-i})+\varepsilon\ \text{ for every } x_i\in X_i \text{ with } (x_i,x^*_{-i})\in\mathbb X .$$
--
--   Because the first two blocks of $g_i$ are $x_{-i}$ and $-x_{-i}$, a point can dominate $g_i(x^*)-\varepsilon\bar c_i$ only if it keeps the other players' strategies fixed; this is the per-player step behind Theorem 3.2, and with $\varepsilon=0$ it gives Theorem 3.1.
--
--   Differences from the source:
--   - generalization: ε > 0 → every real ε; reason: the argument does not use the sign of ε; ε > 0 is a special case
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, proof of Theorem 3.2, pp.4–5

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **ε-Pareto optimality for problem (3) is a unilateral ε-best response.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, proof of Theorem 3.2, pp.4–5: "by Definition 2.4,
x∗ ∈ ǫ argMin{(x−i, −x−i, fi(x))|x ∈ X} is equivalent to: there does not exists an x ∈ X such that
x−i = x∗−i and fi(x) < fi(x∗) − ǫ. This is equivalent to fi(xi, x∗−i) + ǫ ≥ fi(x∗) for any
xi ∈ Xi such that (xi, x∗−i) ∈ X."

For every player `i`, every real `ε` and every joint strategy `x*`, `x*` is ε-Pareto optimal for
problem (3) with respect to `c̄ᵢ = (0, 0, 1)` iff `x* ∈ X` and
`fᵢ(x*) ≤ fᵢ(xᵢ, x*₋ᵢ) + ε` for every `xᵢ` with `(xᵢ, x*₋ᵢ) ∈ X`.

**Formalization Note.** No assumption on `f` or `X`. Stated for every real `ε` (the paper's
`ε > 0`; `ε = 0` is Pareto optimality). `(xᵢ, x*₋ᵢ)` is `Function.update xs i xi`. -/
theorem epsArgMin_iff {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (i : ι) (ε : ℝ) (xs : Joint n) :
    xs ∈ epsArgMin (g n f i) X (cbar n i) ε ↔
      xs ∈ X ∧ ∀ xi : Fin (n i) → ℝ, Function.update xs i xi ∈ X →
        f i xs ≤ f i (Function.update xs i xi) + ε := by sorry

end ApproxNashSet
