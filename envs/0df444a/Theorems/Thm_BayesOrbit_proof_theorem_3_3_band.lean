-- Prove2me | Theorems.Thm_BayesOrbit_proof_theorem_3_3_band
-- name    : BayesOrbit.proof_theorem_3_3_band
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:08.562979+00:00
-- url     : https://prove2.me/theorems/bfe916a7-c0fb-49ac-bd65-ebf2d92ca9aa
-- title:
--   Proof of Theorem 3.3 — band estimate: the orbit meets every multiplicative band around an interior target (corrected: $0<\varepsilon<1$)
-- statement:
--   Let $r$ be a generic signalling structure with $|K|\le|M|$, let $p,q\in\Delta^0(K)$ and $0<\varepsilon<1$. There is a point $q'$ in the orbit of $p$ under $G$ such that, for every $k\in K$,
--   $$
--   q[k]\,\frac{1-\varepsilon}{1+\varepsilon}<q'[k]<q[k]\,\frac{1+\varepsilon}{1-\varepsilon}.
--   $$
--
--   Letting $\varepsilon\to0$ gives points of the orbit converging to any interior target, which is how the paper concludes density.
--
--   Differences from the source:
--   - correction: an arbitrary ε > 0 → 0 < ε < 1; reason: at ε = 2 the upper bound is −3q[k] < 0 < q′[k], so the claim is false, and at ε = 1 it divides by zero; density uses small ε only
--   - encoding: a finite set M with at least two signals (§2.2) → no hypothesis on the number of signals; reason: genericity forces at least two signals when K is non-empty (proved in the sanity file), and for K empty there is no p; same instances
-- source:
--   Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted manuscript (Enlighten 227272), proof of Theorem 3.3, p.16

import Mathlib
import Definitions.Def_BayesOrbit_Model

namespace BayesOrbit

/-- Band estimate of the proof of Theorem 3.3 of Hellman–Levy, Dense Orbits of the Bayesian
Updating Group Action, accepted manuscript (Enlighten 227272), proof of Theorem 3.3, p.16 (PDF 17),
corrected: for interior `p, q` and `0 < ε < 1` there is `q'` in the orbit of `p` with
`q (1 - ε)/(1 + ε) < q' < q (1 + ε)/(1 - ε)` coordinate-wise.

**Formalization Note.** The proof takes an arbitrary `ε > 0`. For `ε ≥ 1` the claim is false or
undefined (at `ε = 2` the upper bound is negative, at `ε = 1` it divides by zero, here `0`), so `ε`
is restricted to `(0, 1)`, which is all that density uses. -/
theorem proof_theorem_3_3_band {K M : Type*} [Fintype K] [Fintype M]
    (S : SignallingStructure K M) (hS : S.IsGeneric)
    (hcard : Fintype.card K ≤ Fintype.card M)
    (p q : stdSimplex ℝ K) (hp : IsInterior p) (hq : IsInterior q)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ q' ∈ S.orbit p, ∀ k,
      (q : K → ℝ) k * ((1 - ε) / (1 + ε)) < (q' : K → ℝ) k ∧
      (q' : K → ℝ) k < (q : K → ℝ) k * ((1 + ε) / (1 - ε)) := by sorry

end BayesOrbit
