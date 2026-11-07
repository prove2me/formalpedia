-- Prove2me | Theorems.Thm_EllipsoidFitting_theorem_1_1_1_2
-- name    : EllipsoidFitting.theorem_1_1_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:22.868333+00:00
-- url     : https://prove2.me/theorems/6ffb485c-f408-4473-92ed-484dd3d1f0f8
-- title:
--   Theorems 1.1 and 1.2 — sharp phase transition at $m=d^2/4$
-- statement:
--   Let $v_1,\dots,v_{m}\sim N(0,I_d/d)$ be independent Gaussian vectors in $\mathbb R^d$, and say they **fit** if some positive semidefinite $\Lambda$ satisfies $v_i^\top\Lambda v_i=1$ for all $i$ (a centered, possibly degenerate ellipsoid through all points). There is a sequence $\varepsilon_d\to0$ such that for every sequence $m=m(d)$:
--
--   1. if $m(d)\le(1-\varepsilon_d)\,d^2/4$ for all large $d$, then
--   $$
--   \mathbb P\bigl[v_1,\dots,v_{m(d)}\ \text{do not fit}\bigr]\longrightarrow0;
--   $$
--   2. if $m(d)\ge(1+\varepsilon_d)\,d^2/4$ for all large $d$, then
--   $$
--   \mathbb P\bigl[v_1,\dots,v_{m(d)}\ \text{fit}\bigr]\longrightarrow0.
--   $$
--
--   This settles the Saunderson–Chandrasekaran–Parrilo–Willsky conjecture: the feasibility threshold of the ellipsoid fitting SDP is $d^2/4$ up to a $1\pm o(1)$ factor.
--
--   **Formalization Note** One sequence $\varepsilon$ serves both sides and every $m(d)$. Probabilities are the (outer) measure of the event under the product law `pointLaw d (m d)`.
--
--   Differences from the source:
--   - reading: m ≤ (1 − o_d(1))·d²/4 … with probability 1 − o_d(1) → ∃ ε : ℕ → ℝ with ε_d → 0, chosen before m, such that for every m : ℕ → ℕ with the bound for all large d the probability of the bad event tends to 0; reason: the strong reading of o_d(1): one vanishing sequence for every m(d); an ε chosen after m would be weaker
--   - encoding: probability of an event → the measure of the complementary (bad) set under the product law, tending to 0; reason: outer measure needs no measurability proof; for measurable events it is the same statement
--   - encoding: an ellipsoid passes through the points → Fits v: a PSD Λ with v_iᵀΛv_i = 1 for all i; reason: the problem statement on p.2 defines it so (origin-centered, possibly degenerate)
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Theorems 1.1 and 1.2, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_EllipsoidFitting_Fits
import Definitions.Def_EllipsoidFitting_pointLaw

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory Filter Topology

/-- **Theorems 1.1 and 1.2 (sharp phase transition at `d²/4`).** de la Cerda, Potechin, Tulsiani,
Xu, *Sharp Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026),
Theorems 1.1 and 1.2, p.3: "Let m ≤ (1 − od(1)) · d2/4 and let v1, . . . , vm ∼ N (0, Id/d) be
independent d-dimensional Gaussian vectors. Then, with probability 1 − od(1), there exists an
ellipsoid passing through all m points." and "Let m ≥ (1 + od(1)) · d2/4 … Then, with probability
1 − od(1), there does not exist any ellipsoid passing through all m points."

There is one sequence `ε_d → 0` such that for every `m : ℕ → ℕ`:
* if `m(d) ≤ (1 − ε_d) d²/4` for all large `d`, the probability that the `m(d)` points admit no
  fitting ellipsoid tends to `0`;
* if `m(d) ≥ (1 + ε_d) d²/4` for all large `d`, the probability that they admit one tends to `0`.

**Formalization Note** "o_d(1)" is a sequence `ε : ℕ → ℝ` tending to `0`, chosen once, before
`m(d)` and for both sides. The probability is the (outer) measure of the event under
`pointLaw d (m d)`, the law of `m(d)` i.i.d. `N(0, I_d/d)` points. An ellipsoid is a PSD `Λ` with
`v_iᵀ Λ v_i = 1` (`Fits`). -/
theorem theorem_1_1_1_2 :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∀ m : ℕ → ℕ,
      ((∀ᶠ d in atTop, (m d : ℝ) ≤ (1 - ε d) * (d : ℝ) ^ 2 / 4) →
        Tendsto (fun d => pointLaw d (m d) {v | ¬ Fits v}) atTop (𝓝 0)) ∧
      ((∀ᶠ d in atTop, (1 + ε d) * (d : ℝ) ^ 2 / 4 ≤ (m d : ℝ)) →
        Tendsto (fun d => pointLaw d (m d) {v | Fits v}) atTop (𝓝 0)) := by sorry

end EllipsoidFitting
