-- Prove2me | Theorems.Thm_AnalystRanking_Revelation_proposition_5_B1_competition_decreases_informativeness
-- name    : AnalystRanking.Revelation.proposition_5_B1_competition_decreases_informativeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:56:18.725991+00:00
-- url     : https://prove2.me/theorems/654a46ac-f744-4767-b0af-be2ce9214266
-- title:
--   Proposition 5 (B.1): competition lowers informativeness iff $\varphi>1$, $\rho>0$ and uncertainty is high, more so with convexity (corrected: $q$-range and convexity clause)
-- statement:
--   Standing assumptions (§2): $\gamma\in(\tfrac12,1)$, $\rho\in[0,1]$, $q\in(0,1)$, and rank payoffs $w_1>w_0>w_2$ with convexity $\varphi=(w_1-w_0)/(w_0-w_2)$. Let $W>0$ be the benchmark prize, and suppose the payoff structure is not linear, $\varphi\neq1$. Write $\Pi$ for forecast informativeness (Definition 3), $e_B$ for the most informative benchmark equilibrium and $e$ for the most informative equilibrium under competition (Definitions 1–2). Then $e_B$ exists, and:
--
--   1. **(Characterization.)** Some most informative competition equilibrium $e$ satisfies $\Pi(e)<\Pi(e_B)$ if and only if
--   $$\varphi>1,\qquad \rho>0,\qquad 1-\gamma\le q\le\gamma,\qquad \check q_{\min}(\varphi)<\max(q,1-q),$$
--   where $\check q_{\min}(\varphi)=\gamma-\rho\gamma(1-\gamma)\frac{\varphi-1}{(1-\gamma)\varphi+\gamma}$ (B.2).
--   2. **(Convexity.)** If $1<\varphi<\varphi'$ are the convexities of two payoff triples and $1-\gamma\le q\le\gamma$, then the most informative equilibria $e$ (at $\varphi$) and $e'$ (at $\varphi'$) exist and the decrease $\Delta\Pi^-=\Pi(e_B)-\Pi(e)$ satisfies
--   $$\Pi(e_B)-\Pi(e)\le\Pi(e_B)-\Pi(e'),$$
--   strictly when $\check q_{\min}(\varphi')<\max(q,1-q)<\gamma$.
--
--   For $q\ge\tfrac12$ the condition of part 1 reads $\check q_{\min}<q\le\gamma$: under convex payoffs and correlated signals, competition makes analysts understate their signals at high prior uncertainty, so their forecasts reveal less than without competition, and the loss grows with the convexity of the rank payoff.
--
--   Differences from the source:
--   - correction: competition decreases information revelation iff φ > 1, ρ > 0 and q < γ (for q ⩾ 1/2) → iff φ > 1 ∧ 0 < ρ ∧ 1 − γ ≤ q ≤ γ ∧ q̌min(φ) < max(q, 1 − q); reason: false in both directions: γ = 0.55, ρ = 0.05, (w1,w0,w2) = (2,0,−1) (φ = 2, q̌min ≈ 0.5415): at q = 0.52 < γ the equilibrium is (1,1) and Π = Π_B; at q = γ it is (1, 1/(1+ρ)) and Π ≈ 0.01739 < Π_B ≈ 0.01905. The proof (p. 60) and discussion (p. 26) give exactly (q̌min, γ] (regime A.1) and [1/2, γ] (regime A.2, q̌min ≤ 1/2)
--   - correction: the decrease in information revelation increases with payoff convexity (proof: ∂ΔΠ⁻/∂φ > 0 on (q̌min, γ]) → for 1 < φ < φ′ and 1 − γ ≤ q ≤ γ: Π(eB) − Π(e) ≤ Π(eB) − Π(e′), strictly when q̌min(φ′) < max(q,1−q) < γ; reason: at q = γ the equilibrium σ̌l(γ) = 1/(1+ρ) does not depend on φ (γ = 0.55, ρ = 0.05: Π = 0.0173918 for φ = 1.5, 2, 5, 50), so the strict claim fails there; the equilibrium jumps at q̌min(φ) = q, so the comparison is between two payoff structures rather than a derivative
--   - generalization: results stated for q ⩾ 1/2 ('Results for q < 1/2 are symmetric') → every q ∈ (0,1), through max(q, 1 − q); reason: at q ⩾ 1/2, max(q, 1 − q) = q and the statement is the printed half
--   - reading: Π_{φ>1} < Π_B for the most informative equilibria → ∃ e most informative under competition with Π(e) < Π(eB), and ∃ eB most informative in the benchmark; reason: Definition 2's e* need not exist in general (e.g. φ = 0.2, γ = 0.6, ρ = 0.1, q = 0.64); where it exists this is the paper's comparison, and when the condition holds the statement asserts it exists
--   - reading: ℰ = the set of all equilibria (Definition 2), with symmetric equilibria and σh ⩾ 1 − σl (p. 9) → IsCompEq / IsBenchEq: symmetric σ ∈ [0,1]² with σh ≥ 1 − σl, each signal type best-responding against every mixed deviation, Bayes beliefs; reason: the paper restricts attention to these profiles on p. 9 and calls them the equilibria
--   - reading: display before (1), p. 7: Pr(si, sj | ω) = 2(1 − ρ)γ(1 − γ) if si ≠ sj → (1 − ρ)γ(1 − γ) for each ordered discordant pair, per (1)–(2); reason: the printed value is the probability of the event si ≠ sj; per ordered pair only (1)–(2) sum to 1
--   - encoding: signals {h,l}, forecasts {ĥ,l̂}, states {H,L}; strategy (σh, σl); payoffs w1 > w0 > w2 of (3) → Bool with true the high value; σ : ℝ × ℝ; the payoff triple (w1, w0, w2) with φ = phiConvexity w1 w0 w2; reason: Lean convention; same instances
--   - encoding: Π with H = 1, L = 0 (p. 24) → informativeness, with x/0 = 0 for a forecast pair of probability 0; reason: such a pair contributes 0 to the expected posterior variance, its true contribution
-- source:
--   Banerjee, Does Competition Improve Analysts' Forecast Informativeness?, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 5 (B.1), p. 25 (with the preamble 'Proposition 5 summarizes results for q ⩾ 1/2. Results for q < 1/2 are symmetric.'); proof pp. 59–60; discussion p. 26

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_IsCompEq
import Definitions.Def_AnalystRanking_Revelation_IsBenchEq
import Definitions.Def_AnalystRanking_Revelation_IsMostInformative
import Definitions.Def_AnalystRanking_Revelation_informativeness
import Definitions.Def_AnalystRanking_Revelation_qminCheck
import Definitions.Def_AnalystRanking_Revelation_phiConvexity

namespace AnalystRanking.Revelation

/-- **Proposition 5 (B.1): competition lowers forecast informativeness iff payoffs are convex,
signals correlated and prior uncertainty high; the loss grows with convexity (corrected).**
Banerjee, *Does Competition Improve Analysts' Forecast Informativeness?*, Alberta School of Business Research Paper No. 2017-311 (November 13, 2017), Proposition 5 (B.1), p. 25: "Suppose that analysts' payoff structure is not linear; i.e.,
`φ ≠ 1`. Then, B.1) competition decreases analysts' information revelation if and only if their
payoff structure is convex, their signals are positively correlated conditional on the state, and
the prior uncertainty is high; i.e., `φ > 1`, `ρ > 0` and `q < γ`. Furthermore, the decrease in
information revelation increases with payoff convexity". Preamble, p. 25: "Proposition 5
summarizes results for `q ⩾ 1/2`. Results for `q < 1/2` are symmetric." The comparison is between
`Π` (Definition 3, (6)) of the most informative equilibrium (Definition 2) under competition and
under the benchmark (§3.1); the decrease is `ΔΠ⁻ ≡ Π_B − Π_{φ>1}` (proof, p. 60).

The statement asserts that the benchmark's most informative equilibrium `e_B` exists, and:
1. some most informative competition equilibrium `e` has `Π(e) < Π(e_B)` iff
   `φ > 1`, `ρ > 0`, `1 − γ ≤ q ≤ γ` and `q̌_min(φ) < max(q, 1 − q)`;
2. for payoff triples with `1 < φ < φ′` and `1 − γ ≤ q ≤ γ`, the most informative equilibria
   `e`, `e′` exist and `Π(e_B) − Π(e) ≤ Π(e_B) − Π(e′)`, strictly when
   `q̌_min(φ′) < max(q, 1 − q) < γ`.

**Formalization Note.** Corrections: (a) the printed range "`q < γ`" (for `q ≥ 1/2`) is false in
both directions: with `γ = 0.55`, `ρ = 0.05`, `(w₁, w₀, w₂) = (2, 0, −1)` (`φ = 2`,
`q̌_min ≈ 0.5415`), at `q = 0.52 < γ` the competition equilibrium is `(1, 1)` and `Π = Π_B`, while
at `q = γ` it is `(1, 1/(1 + ρ))` and `Π ≈ 0.01739 < Π_B ≈ 0.01905`; the proof (p. 60) and the
discussion (p. 26) give exactly `(q̌_min, γ]` (regime A.1) and `[1/2, γ]` (regime A.2, where
`q̌_min ≤ 1/2`). (b) "The decrease increases with payoff convexity" fails strictly at `q = γ`,
where `σ̌ˡ(γ) = 1/(1 + ρ)` does not depend on `φ`; it is stated weakly on `[1 − γ, γ]` and strictly
where the decrease is driven by `σ̌ˡ` or `σ̇`. Generalization: all `q ∈ (0, 1)` through
`max(q, 1 − q)` (the preamble's symmetric half). Reading: Definition 2's `e*` exists exactly when
asserted; the left side of the equivalence quantifies over most informative equilibria. -/
theorem proposition_5_B1_competition_decreases_informativeness
    (γ ρ q W w1 w0 w2 : ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hW : 0 < W) (hw20 : w2 < w0) (hw01 : w0 < w1) (hφ : phiConvexity w1 w0 w2 ≠ 1) :
    ∃ eB : ℝ × ℝ, IsMostInformative (IsBenchEq W q γ) eB ∧
      ((∃ e : ℝ × ℝ, IsMostInformative (IsCompEq w1 w0 w2 q γ ρ) e ∧
          informativeness q γ ρ e < informativeness q γ ρ eB) ↔
        (1 < phiConvexity w1 w0 w2 ∧ 0 < ρ ∧ 1 - γ ≤ q ∧ q ≤ γ ∧
          qminCheck γ ρ (phiConvexity w1 w0 w2) < max q (1 - q))) ∧
      (∀ w1' w0' w2' : ℝ, w2' < w0' → w0' < w1' →
        1 < phiConvexity w1 w0 w2 → phiConvexity w1 w0 w2 < phiConvexity w1' w0' w2' →
        1 - γ ≤ q → q ≤ γ →
        ∃ e e' : ℝ × ℝ, IsMostInformative (IsCompEq w1 w0 w2 q γ ρ) e ∧
          IsMostInformative (IsCompEq w1' w0' w2' q γ ρ) e' ∧
          informativeness q γ ρ eB - informativeness q γ ρ e ≤
            informativeness q γ ρ eB - informativeness q γ ρ e' ∧
          (qminCheck γ ρ (phiConvexity w1' w0' w2') < max q (1 - q) → max q (1 - q) < γ →
            informativeness q γ ρ eB - informativeness q γ ρ e <
              informativeness q γ ρ eB - informativeness q γ ρ e')) := by sorry

end AnalystRanking.Revelation
