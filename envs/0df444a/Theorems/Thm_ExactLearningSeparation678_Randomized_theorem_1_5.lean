-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_theorem_1_5
-- name    : ExactLearningSeparation678.Randomized.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:55.434123+00:00
-- url     : https://prove2.me/theorems/8e994f9d-441e-460d-aec2-c73fec536e66
-- title:
--   Theorem 1.5 — optimal randomized versus quantum exact learning separation
-- statement:
--   Let $C_t$ be the full class of Definition 3.1 for $t=2^m$, $m\ge2$, and let $Q_t=Q(C_t)$ and $R_t=R(C_t)$ be the actual bounded-error quantum and randomized membership-query complexities. Every class is nonempty and has coordinate domain of size $N_t=t^{14}+t^{13}$. Then
--   $$Q_t\longrightarrow\infty,\qquad
--   R_t\ge c\,\frac{Q_t^3\log N_t}{\log Q_t}\quad(m\ge m_0),$$
--   for some absolute $c>0$ and $m_0$, with $Q_t>1$ throughout this eventual range. Divergence means that for every integer bound $B$, all sufficiently large exponents have $Q_t\ge B$.
--
--   This explicit family witnesses the paper's full existential separation. Success means identification of the whole Boolean concept with probability at least $2/3$ for every target; both oracle parts are available to all learners. No asymptotic bound on a user-supplied family is assumed.
--
--   **Formalization Note** Logarithms are natural, the true coordinate count is retained inside the logarithm, and all constants and thresholds precede the exponent over which they are uniform.
--
--   Differences from the source:
--   - encoding: t ≥ 4 is a power of two, with a fixed binary basis of F_(t^6) → m is a natural number at least 2, t = 2^m, F = GaloisField 2 (6m), with a chosen genuine binary basis and F₂-valued binary labels; reason: this realizes every permitted size and fixes the coordinate convention of Definition 3.1
--   - encoding: there exist concept classes with Q(C)=ω(1) and R(C)=Ω(Q(C)³ log N / log Q(C)) → the explicit Definition 3.1 family is nonempty with its true domain cardinality, Q tends to infinity, and one c>0 and one threshold work for every later exponent; reason: the proof supplies this witness family; the explicit quantifiers retain the entire existential asymptotic conclusion
--   - encoding: binary logarithms implicit in the coordinate convention, with the goal using log N / log Q → natural logarithms, and eventual Q_t > 1 stated alongside the separation; reason: the change-of-base factor cancels in log N / log Q; Q→∞ supplies eventual Q > 1 and hence a positive denominator
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 1.5, p.3 and §3.5, p.28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Construction

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized

/-- Theorem 1.5, pp.3 and 28: the explicit constructed witness family has Q→∞ and the full cubic logarithmic separation in the actual randomized and quantum query minima. Natural logarithms; true domain size t^14+t^13. The constants precede all growing parameters. -/
theorem theorem_1_5 :
    (∀ m : Size, (conceptClass m).Nonempty ∧ Fintype.card (Domain m) = N m) ∧
    (∀ B : ℕ, ∃ M : ℕ, ∀ m : Size, M ≤ m.val → B ≤ Q m) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m : Size, m₀ ≤ m.val →
      1 < Q m ∧ c * (Q m : ℝ) ^ 3 * Real.log (N m : ℝ) / Real.log (Q m : ℝ) ≤
        (R m : ℝ)) := by sorry

end ExactLearningSeparation678.Randomized
