-- Prove2me | Theorems.Thm_BilateralProfit_claim_4_10
-- name    : BilateralProfit.claim_4_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:19:09.38063+00:00
-- url     : https://prove2.me/theorems/8486bcdd-a2ab-4ab2-b5d8-10dbc9cdd64f
-- title:
--   Claim 4.10 — uniform estimation of monotone functions from noisy queries
-- statement:
--   There is an absolute constant $C$ with the following property. Let $Y$ be a finite totally ordered set and $G$ a finite family of functions, each $g\in G$ defined on a subset $Y_g\subseteq Y$, monotone (non-decreasing or non-increasing) on $Y_g$, with values in $[-1,1]$, and with total variations satisfying $\sum_{g\in G}\mathrm{TV}(g)\le W$ for a known constant $W$. For each $g$ and $y\in Y_g$, the $n$-th query at $g(y)$ reveals the $n$-th variable $Z^{(n)}_{g,y}$ of a sequence of mutually independent random variables with expectation $g(y)$ and values in a common interval of length at most $4$. Then for every $\alpha,\delta'\in(0,1)$ there is a procedure, depending only on $Y$, the domains $Y_g$, $W$, $\alpha$ and $\delta'$, that makes at most
--   $$C\,\frac{\log(2|G||Y|/\delta')}{\alpha^2}\Big(|G|+\frac W\alpha\log(2|Y|)\Big)$$
--   queries on every run and, with probability at least $1-\delta'$, outputs estimates $\hat g$ with $|\hat g(y)-g(y)|\le\alpha$ for every $g\in G$ and $y\in Y_g$.
--
--   In the proof of Lemma 4.8 this is applied to the monotone pieces of the telescoping decomposition (21).
--
--   **Formalization Note** $G$ is indexed by a finite type; the procedure is a deterministic adaptive routine that queries only pairs $(g,y)$ with $y\in Y_g$. $\mathrm{TV}$ is the variation on $Y_g$. The common interval is $[c,c+4]$.
--
--   Differences from the source:
--   - generalization: a set $G$ of functions → a finite family indexed by a type $\iota$ (repetitions allowed); reason: an injective indexing is the paper's set; a family with repetitions is estimated by treating each index separately
--   - reading: "there exists a procedure" using at most the stated number of queries; $C$ an absolute constant → a deterministic adaptive routine chosen from $(\iota,Y,\text{domains},W,\alpha,\delta')$ before the functions and the observation laws, querying only inside the domains, with the query bound on every run; $C$ chosen first; reason: the proof's procedure is deterministic, queries domain points only, and is forced to halt deterministically after the bound (80) (p.58)
--   - encoding: $W$ a known constant with $\sum_g\mathrm{TV}(g)\le W$ → hypothesis $0\le W$; reason: total variations are non-negative, so for $W<0$ the hypothesis has no instance; the Lean order states the query bound before the functions
--   - encoding: values in a common interval of length at most $4$; probability at least $1-\delta'$ → laws carried by $[c,c+4]$ for one $c$; $\mathrm{ofReal}(1-\delta')\le$ the routine's success probability; reason: same instances; probabilities in $[0,\infty]$
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Claim 4.10, p.27 (PDF 29); proof in App. A.4, pp.57–58 (PDF 59–60)

import Mathlib
import Definitions.Def_BilateralProfit_QueryRoutine

namespace BilateralProfit

open MeasureTheory

/-- **Claim 4.10**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.27
(PDF 29), proof in App. A.4, pp.57–58: uniform estimation of monotone functions.

Let `G` be a finite family of monotone functions `g`, each defined on a subset of a finite
ordered domain `Y` with values in `[−1, 1]`, with `Σ_{g ∈ G} TV(g) ≤ W` for a known constant `W`.
Each query at `g(y)` reveals the next unused variable of a sequence of mutually independent
random variables with expectation `g(y)` and values in a common interval of length at most `4`.
Then for `α, δ′ ∈ (0, 1)` there is a procedure that estimates every function uniformly to error
`α`, simultaneously with probability at least `1 − δ′`, using at most
`C log(2|G||Y|/δ′)/α² · (|G| + (W/α) log(2|Y|))` queries, `C` an absolute constant.

**Formalization Note.** `G` is indexed by a finite type `ι`; `dom i ⊆ Y` is the (known) domain of
the `i`-th function. The procedure is a routine `R` (`QTree`) chosen from `ι, Y, dom, W, α, δ′`
only; it queries pairs `(i, y)` with `y ∈ dom i`, at most `N` times on every run, and works for
every family `g` and every observation law with the stated properties. "Monotone" is
non-decreasing or non-increasing on the domain; `TV(g)` is `eVariationOn` on the domain. The
common interval is `[c, c + 4]` for some `c`. `0 ≤ W` (a bound on a sum of total variations). -/
theorem claim_4_10 :
    ∃ C : ℝ, ∀ (ι Y : Type) [Fintype ι] [DecidableEq ι] [Fintype Y] [LinearOrder Y]
      (dom : ι → Finset Y) (W α δ : ℝ), 0 ≤ W → 0 < α → α < 1 → 0 < δ → δ < 1 →
      ∃ (R : QTree (ι × Y) (ι → Y → ℝ)) (N : ℕ),
        (N : ℝ) ≤ C * Real.log (2 * Fintype.card ι * Fintype.card Y / δ) / α ^ 2 *
          (Fintype.card ι + W / α * Real.log (2 * Fintype.card Y)) ∧
        R.QueriesAtMost N ∧ R.AllQueries (fun q => q.2 ∈ dom q.1) ∧
        ∀ g : ι → Y → ℝ, (∀ i, ∀ y ∈ dom i, g i y ∈ Set.Icc (-1 : ℝ) 1) →
          (∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) →
          ∑ i, (eVariationOn (g i) ↑(dom i)).toReal ≤ W →
          ∀ (c : ℝ) (obs : ι × Y → ℕ → Measure ℝ),
            (∀ i, ∀ y ∈ dom i, ∀ n, IsProbabilityMeasure (obs (i, y) n)) →
            (∀ i, ∀ y ∈ dom i, ∀ n, obs (i, y) n (Set.Icc c (c + 4))ᶜ = 0) →
            (∀ i, ∀ y ∈ dom i, ∀ n, ∫ r, r ∂(obs (i, y) n) = g i y) →
            ENNReal.ofReal (1 - δ) ≤
              R.prob obs (fun est => ∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) (fun _ => 0) := by sorry

end BilateralProfit
