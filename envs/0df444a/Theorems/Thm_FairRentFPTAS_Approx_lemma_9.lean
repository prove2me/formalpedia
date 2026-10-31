-- Prove2me | Theorems.Thm_FairRentFPTAS_Approx_lemma_9
-- name    : FairRentFPTAS.Approx.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:43.509991+00:00
-- url     : https://prove2.me/theorems/b38b2c1e-b024-46ee-93fb-2ee44513e47d
-- title:
--   Lemma 9 (Approximation Guarantee), p. 17 — every envy-free solution of Ī is ε-EF for I
-- statement:
--   Let $\varepsilon\in(0,1)$ and let $\mathcal I$ be an instance with continuous, strictly decreasing piecewise-linear utilities. The slope-rounded instance $\bar{\mathcal I}$ satisfies:
--   1. its utilities are continuous, strictly decreasing and piecewise linear;
--   2. all its slopes are integer powers of $(1+\varepsilon)$;
--   3. every envy-free solution $(\pi,p)$ of $\bar{\mathcal I}$ with $p\ge0$ is an $\varepsilon$-EF solution of $\mathcal I$:
--   $$\bar v_a(\pi(a),p_{\pi(a)})\ge\bar v_a(r,p_r)\ \forall a,r\quad\Longrightarrow\quad(\pi,p)\text{ is }\varepsilon\text{-EF for }\mathcal I.$$
--
--   Together with Theorem 1 this gives the approximation scheme of Theorem 2.
--
--   **Formalization Note** "We can efficiently construct" is not formalized; $\bar{\mathcal I}$ is the explicit construction of the definitions file. Rents are nonnegative, the paper's standing convention for solutions (p. 7).
-- source:
--   Arunachaleswaran, Barman & Rathi, Fully Polynomial-Time Approximation Schemes for Fair Rent Division, arXiv:1807.04163v1, p. 17, Lemma 9

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

namespace FairRentFPTAS.Approx

/-- Lemma 9, p. 17: for `ε ∈ (0, 1)` the slope-rounded instance `Ī` has well-formed utilities,
all slopes integer powers of `(1+ε)`, and every envy-free solution of `Ī` with nonnegative rents
is an `ε`-EF solution of `I`. -/
theorem lemma_9 {n : ℕ} (I : Instance n) (ε : ℝ) (hI : Standing I) (hε : 0 < ε) (hε1 : ε < 1) :
    Standing (roundInst ε I) ∧ PowersProp ε (roundInst ε I) ∧
      ∀ (π : Equiv.Perm (Fin n)) (p : Fin n → ℝ), (∀ r, 0 ≤ p r) →
        IsEF (roundInst ε I) π p → IsEpsEF I ε π p := by sorry

end FairRentFPTAS.Approx
