-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_E_2
-- name    : BlottoFPTAS.Main.lemma_E_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:43:23.618114+00:00
-- url     : https://prove2.me/theorems/5387ebb8-faf7-466f-9582-e63a615fd245
-- title:
--   Lemma E.2 — a rational ρ chosen from b, m, e only, with denominator ≤ q, for which an anchor table in P(γ), γ > β, with O(log H)-bit entries exists whenever one must change
-- statement:
--   Under the standing assumption $0<b<1$ of §5: there are a universal constant $C_0$, a rule choosing $\rho$ from $(b,m,e)$ only, and a rule naming which anchor table, if any, must change, such that $\rho\in(0,1)$ has denominator at most $q=2\,\mathrm{pow2ceil}(4H^2)$, with
--   $$\log_2q\le C_0\,d\log_2(m+3)+C_0,\qquad \log_2q\le C_0\tfrac me\log_2(m+2)+C_0;$$
--   if no table changes then $\rho=b$; if A's table changes then $\rho<b$ and the opposing budgets are $\beta_0=\rho<\beta=b$; if B's table changes then $\rho>b$ and $\beta_0=1/\rho<\beta=1/b$. If a table must change, then for every label table (every label of probability $1/K$ on every battlefield), every anchor table $u$ obtained at this $\rho$ (static constraints) and any positive values summing to one, either no tuple has score greater than $h^*$, or some anchor table in $P(\gamma)$ for some $\gamma>\beta$ has rational entries of binary length at most $C_0\log_2H+C_0$. Because the bound is uniform over all tables, $\rho$ can be fixed before either strategy is computed.
--
--   Differences from the source:
--   - reading: Using only b, m and e, the algorithm selects ρ and determines which anchor table must change; … computes an anchor table → there exist functions ρsel(b, m, a) and which(b, m, a), and the anchor table exists; reason: the selection procedure of App. E.3 and the computation of App. E.4 are not formalized; their outcome is the content
--   - reading: O(d log(m + 3)), O((m/e) log(m + 2)), O(log H) bits → explicit bounds with one universal constant C₀; reason: standard reading of O
--   - generalization: for the rows and scores later obtained at this ρ → for every label table with each label of probability 1/K (any number of rows), every anchor table with the static constraints, and any positive values summing to one; reason: the bound of App. E.2 holds for every label table and score threshold (p. 66); the tables obtained are a special case
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 65, Lemma E.2

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Anchors

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma E.2** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 65), read
as an existence statement, under the standing assumption `b < 1` of §5 (p. 29). There are a universal constant `C₀`, a rule `ρsel` choosing `ρ` from
`(b, m, a)` only (`e = 2^{-a}`), and a rule `which` naming the anchor table that must change
(`none`: neither, and then `ρ = b`; `some false`: A's, and then `ρ < b`, opposing budgets
`β₀ = ρ < β = b`; `some true`: B's, and then `ρ > b`, `β₀ = 1/ρ < β = 1/b`), such that `ρ ∈ (0, 1)`
has denominator at most `q = 2 pow2ceil(4H²)`, `log₂ q ≤ C₀ d log₂(m + 3) + C₀` and
`log₂ q ≤ C₀ (m/e) log₂(m + 2) + C₀`, and, if a table must change, then for every label table
(every label of probability `1/K` on every battlefield) and every anchor table `u` obtained at this
`ρ` (static constraints), with scores from any positive values summing to one, either no tuple has
score greater than `h*` or some anchor table in `P(γ)` for some `γ > β` has rational entries of
binary length at most `C₀ log₂ H + C₀`. -/
theorem lemma_E_2 :
    ∃ (C₀ : ℝ) (ρsel : ℚ → ℕ → ℕ → ℚ) (which : ℚ → ℕ → ℕ → Option Bool),
      ∀ (b : ℚ) (m a : ℕ), 0 < b → b < 1 → 2 ≤ m → 1 ≤ a →
        let ρ := ρsel b m a
        0 < ρ ∧ ρ < 1 ∧ ρ.den ≤ qDen m a ∧
        Real.logb 2 (qDen m a) ≤ C₀ * dAnch m a * Real.logb 2 (m + 3) + C₀ ∧
        Real.logb 2 (qDen m a) ≤ C₀ * (m / eR a) * Real.logb 2 (m + 2) + C₀ ∧
        (which b m a = none → ρ = b) ∧
        (which b m a = some false → ρ < b) ∧
        (which b m a = some true → b < ρ) ∧
        ∀ who : Bool, which b m a = some who →
          let β₀ : ℝ := if who then 1 / (ρ : ℝ) else (ρ : ℝ)
          let β : ℝ := if who then 1 / (b : ℝ) else (b : ℝ)
          ∀ (w : Fin m → ℝ), (∀ j, 0 < w j) → ∑ j, w j = 1 →
          ∀ (R : ℕ) (lab : Fin R → Fin m → Fin (Klab a)), 0 < R → EachLabelOneOverK a lab →
          ∀ u : Fin m → Fin (Klab a) → ℝ, IsStatic a u lab →
            (∀ l : Fin m → Fin (Klab a), tupleScore a w l ≤ hStar a w u β₀) ∨
            ∃ (γ : ℝ) (u' : Fin m → Fin (Klab a) → ℝ), β < γ ∧ InP a w u β₀ lab γ u' ∧
              ∀ j l, ∃ r : ℚ, u' j l = (r : ℝ) ∧
                (ratSize r : ℝ) ≤ C₀ * Real.logb 2 (Hbd m a) + C₀ := by sorry

end BlottoFPTAS.Main
