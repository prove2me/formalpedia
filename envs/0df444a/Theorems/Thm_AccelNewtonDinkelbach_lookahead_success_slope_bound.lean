-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_lookahead_success_slope_bound
-- name    : AccelNewtonDinkelbach.lookahead_success_slope_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:17:00.655627+00:00
-- url     : https://prove2.me/theorems/c47a91d4-a881-41fc-aa2f-070d1ee84873
-- title:
--   After a successful look-ahead: $0<-2g_+^{(i)}\le -g^{(i-1)}$
-- statement:
--   Let $f:\mathbb R\to\bar{\mathbb R}$ be a proper concave function and let $\delta^{(1)},\dots,\delta^{(N)}$ with supergradients $g^{(1)},\dots,g^{(N)}$ be the iterates of a run of the Newton–Dinkelbach method in which each iteration is a standard update or a successful look-ahead (this covers Algorithm 1). Let $2\le i\le N$ and suppose the look-ahead in iteration $i-1$ was successful, i.e.
--
--   $$\delta^{(i)}=2\Bigl(\delta^{(i-1)}-\frac{f(\delta^{(i-1)})}{g^{(i-1)}}\Bigr)-\delta^{(i-1)} .$$
--
--   Let $g_+^{(i)}$ be the least element of $\partial f(\delta^{(i)})$ (the right derivative of $f$ at $\delta^{(i)}$). Then
--
--   $$0<-2g_+^{(i)}\le -g^{(i-1)} .$$
--
--   After a successful look-ahead the slope at the new point is at most half as steep as the slope used in the previous iteration. In the proof of Lemma 3.4 this yields $D_f(\delta^*,\delta^{(i-1)})>2D_f(\delta^*,\delta^{(i)})$.
--
--   Differences from the source:
--   - encoding: proper concave f : ℝ → R̄ → dom : Set ℝ and f : ℝ → ℝ with ConcaveOn ℝ dom f; reason: x ∉ dom means f(x) = −∞; the effective domain of a proper concave function is convex and the values of f off dom are never used; same instances
--   - encoding: iterations of the algorithm with value and supergradient oracles → 1-indexed run prefixes δ(1..N), g(1..N) (IsRun), with the oracle answers existentially chosen at every call; reason: every execution with any oracle, stopped after any iteration, is such a run, and every such run is an execution prefix
--   - encoding: g ∈ ∂f(δ) on lines 4 and 8 (empty only if f(δ) = −∞) → Newton point in dom with ∂f empty: no next iterate; look-ahead guess in dom with ∂f empty: the look-ahead fails; reason: the page's iteration cannot be executed, resp. its test cannot pass; no execution of the page is excluded
--   - generalization: Algorithm 1 (proof of Lemma 3.4) → every run of RelaxedStep: at each iteration either the standard update or a successful look-ahead, chosen freely; reason: runs of the standard method and of Algorithm 1 are relaxed runs (LookAheadStep implies RelaxedStep), so the statement specializes to both
--   - generalization: i > 2 → 2 ≤ i ≤ N; reason: the claim holds already at i = 2; it specializes to every i > 2
--   - encoding: the look-ahead step in iteration i − 1 was successful → δ(i) = 2 · newtonPoint f (δ(i−1)) (g(i−1)) − δ(i−1); reason: within a run this holds exactly when the successful branch was taken: the standard branch gives δ(i) = d, and d = 2d − δ(i−1) would force f(δ(i−1)) = 0
--   - encoding: g(i)+ = min_{g∈∂f(δ(i))} g → a hypothesis IsLeast (superdiff dom f (δ i)) gp on a variable gp; reason: the statement is about the minimum whenever it exists; its existence is the milestone bregman_right_derivative_form
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8 ("Assume first that the look-ahead step in iteration i − 1 was successful. We now claim that 0 < −2g(i)+ ≤ −g(i−1).")

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_newtonPoint
import Definitions.Def_AccelNewtonDinkelbach_RelaxedStep
import Definitions.Def_AccelNewtonDinkelbach_IsRun

namespace AccelNewtonDinkelbach

/-- **After a successful look-ahead: `0 < −2g₊(i) ≤ −g(i−1)`.**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, proof of Lemma 3.4, p.8: "Assume first that the
look-ahead step in iteration i − 1 was successful. We now claim that 0 < −2g(i)+ ≤ −g(i−1)."

For every proper concave `f` (encoded as `(dom, f)`), every run of relaxed steps, every
`2 ≤ i ≤ N` such that `δ(i)` is the look-ahead point `2(δ(i−1) − f(δ(i−1))/g(i−1)) − δ(i−1)` of
iteration `i − 1`, and every least element `g₊` of `∂f(δ(i))` (the right derivative of `f` at
`δ(i)`): `0 < −2 g₊` and `−2 g₊ ≤ −g(i−1)`.

**Formalization Note** "The look-ahead step in iteration `i − 1` was successful" is written
`δ(i) = 2 d − δ(i−1)` with `d` the Newton point of iteration `i − 1`: within a run this holds exactly
when the successful branch was taken, since the standard branch gives `δ(i) = d`, and `d = 2d − δ(i−1)`
would force `f(δ(i−1)) = 0`. `g₊ = min ∂f(δ(i))` is the hypothesis `IsLeast` on `gp` (its existence
is `bregman_right_derivative_form`). The statement holds for relaxed runs, which include
Algorithm 1; `δ*` does not occur. -/
theorem lookahead_success_slope_bound (dom : Set ℝ) (f : ℝ → ℝ) (hf : ConcaveOn ℝ dom f)
    (δ g : ℕ → ℝ) (N : ℕ) (hrun : IsRun (RelaxedStep dom f) dom f δ g N)
    (i : ℕ) (hi : 2 ≤ i) (hiN : i ≤ N)
    (hsucc : δ i = 2 * newtonPoint f (δ (i - 1)) (g (i - 1)) - δ (i - 1))
    (gp : ℝ) (hgp : IsLeast (superdiff dom f (δ i)) gp) :
    0 < -2 * gp ∧ -2 * gp ≤ -g (i - 1) := by sorry

end AccelNewtonDinkelbach
