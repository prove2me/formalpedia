-- Prove2me | Theorems.Thm_CorrelatedRounding_display_1
-- name    : CorrelatedRounding.display_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-04T05:36:59.429069+00:00
-- url     : https://prove2.me/theorems/bc6fd90e-f053-481d-a8da-8598e6bedbcd
-- title:
--   Display (1) — rewriting the event $Z_i=k$ along a sequence of arrivals
-- statement:
--   Fix an FC $k$, a realization $E$, an output $z$ of Algorithm 1 for $E$, and a strictly increasing real sequence $S^1<S^2<\dots$ with $S^1=E_k$. If $z(i)=k$ then $u_{ki}>0$, and for an item $i$ with $u_{ki}>0$,
--   $$(z(i)=k)\subseteq\Big(\min_{k'}\frac{y_{k'}}{u_{k'i}}E_{k'}\ge\frac{y_k}{u_{ki}}E_k\Big)=\Big(\min_{k'\ne k}\frac{y_{k'}}{u_{k'i}}E_{k'}\ge\frac{y_k}{u_{ki}}S^1\Big)$$
--   $$=\bigcup_{j\ge1}\Big(\min\Big\{\min_{k'\neq k}\frac{y_{k'}}{u_{k'i}}E_{k'},\ \min_{j'<j}\frac{y_k}{u_{ki}}S^{j'}\Big\}\ge\frac{y_k}{u_{ki}}S^j\Big).$$
--   The last union looks vacuous, since its terms with $j>1$ never occur. It is what later lets the event be relaxed and memorylessness be applied.
--
--   Differences from the source:
--   - generalization: S is the random sequence of arrival times of a Poisson process of rate y_k, and the events are random → the chain holds pointwise, for one real vector E and every strictly increasing real sequence S with S 0 = E k; reason: the page's arrivals are strictly increasing almost surely, so the page's chain follows up to a null set
--   - reading: "For all items i with u_ki > 0" → the clause z i = k → 0 < u k i, and 0 < u k i as a hypothesis of the other clauses; reason: the restriction is implicit in the page; the first clause shows that it loses no event
--   - encoding: a minimum on the left of ≥ → the conjunction over its arguments; reason: same event; for K = 1 the minimum over k′ ≠ k is ∞, the empty conjunction
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Theorem 1, display (1), p.11

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output

namespace CorrelatedRounding

/-- **Display (1).** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Theorem 1, p.11:
"(Z_i = k) ⊆ (min_{k′} (y_{k′}/u_{k′i}) E_{k′} ≥ (y_k/u_ki) E_k) = (min_{k′≠k} (y_{k′}/u_{k′i}) E_{k′} ≥ (y_k/u_ki) S¹_k)
= ⋃_{j=1}^∞ (min{min_{k′≠k} (y_{k′}/u_{k′i}) E_{k′}, min_{j′<j} (y_k/u_ki) S^{j′}_k} ≥ (y_k/u_ki) S^j_k)",
for FCs with `u_ki > 0` and with `S¹_k = E_k`.

The four clauses are, in order: the event `Z_i = k` forces `u_ki > 0` (the page's restriction is implicit);
the inclusion; the first equality; the second equality.

**Formalization Note.** The events are stated pointwise, for one real vector `E` and one strictly increasing
real sequence `S` with `S 0 = E k`. Lean's `j = 0` is the page's `j = 1`. The Poisson arrival times of the
page satisfy these conditions almost surely, so the pointwise form specializes to the page's events up to a
null set. A minimum on the left of `≥` is written as the conjunction over its arguments; for `K = 1` the
minimum over `k' ≠ k` is `∞`, which is the empty conjunction. -/
theorem display_1 {q K : ℕ} {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → ℝ}
    {z : Fin q → Fin K} (hz : IsAlg1Output u E z) (k : Fin K) (S : ℕ → ℝ) (hS : StrictMono S)
    (hS0 : S 0 = E k) (i : Fin q) :
    (z i = k → 0 < u k i) ∧
      (0 < u k i → z i = k → ∀ k', clock u E k i ≤ clock u E k' i) ∧
      (0 < u k i → ((∀ k', clock u E k i ≤ clock u E k' i) ↔
        ∀ k', k' ≠ k → ((y u k / u k i * S 0 : ℝ) : EReal) ≤ clock u E k' i)) ∧
      (0 < u k i → ((∀ k', k' ≠ k → ((y u k / u k i * S 0 : ℝ) : EReal) ≤ clock u E k' i) ↔
        ∃ j, (∀ k', k' ≠ k → ((y u k / u k i * S j : ℝ) : EReal) ≤ clock u E k' i) ∧
          ∀ j' < j, y u k / u k i * S j ≤ y u k / u k i * S j')) := by sorry

end CorrelatedRounding
