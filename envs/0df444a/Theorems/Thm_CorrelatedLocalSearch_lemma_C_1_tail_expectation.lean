-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_lemma_C_1_tail_expectation
-- name    : CorrelatedLocalSearch.lemma_C_1_tail_expectation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:01.800044+00:00
-- url     : https://prove2.me/theorems/6cfb111c-ea88-4b56-b319-657aca70e545
-- title:
--   End of the proof of Lemma C.1 — critical tail $\min\{1,CD\lambda^he^{-cT^{1/3}}\}$ and $\mathbb E_\nu\tau\le C(h+\log D+1)^3$
-- statement:
--   Fix integers $k/2<r<k$. There are constants $c,C>0$, depending only on $k$ and $r$, such that for every process satisfying the integer-potential hypotheses of Lemma C.1 with initial potential $h$, every $D\ge1$ and every $\nu\in\mathcal Q_{s_*,D}$:
--
--   1. for every integer $T\ge0$,
--   $$
--   \mathbb P_\nu\{\tau>T\}\ \le\ \min\bigl\{1,\ C D\lambda^h e^{-cT^{1/3}}\bigr\};
--   $$
--   2. $\displaystyle \mathbb E_\nu\tau\ \le\ C\,(h+\log D+1)^3 .$
--
--   These are the critical-threshold halves of (9) and (10) in Theorem 4.1, stated for every integer-potential process.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
--   - encoding: E_ν τ → lower Lebesgue integral ∫⁻ of τ cast from ℕ∞ to ℝ≥0∞; reason: τ is measurable (each {τ > T} is a finite union of cylinders), so this is the expectation, with value ∞ when ν{τ = ∞} > 0
--   - encoding: log D (base not fixed) → natural logarithm Real.log; reason: another fixed base only rescales C
--   - encoding: constants C (tail) and C′ (expectation) → one constant C for both bounds; reason: take the larger of the two
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, end of the proof of Lemma C.1, p.23 (PDF p.25); Lemma C.1, last sentence, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess

set_option autoImplicit false

namespace CorrelatedLocalSearch

open MeasureTheory

/-- The critical tail and the cubic expectation bound (Xu, *Local Search with Correlated
Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, end of the proof of Lemma C.1,
p.23, and the last sentence of Lemma C.1, p.21): for `k/2 < r < k` there are `c, C > 0`
depending only on `k, r` such that, for every process satisfying the hypotheses of Lemma C.1
with initial potential `h`, every `D ≥ 1` and every `ν ∈ Q_{s∗,D}`,
`P_ν{τ > T} ≤ min{1, C D λ^h e^{−c T^{1/3}}}` for every integer `T ≥ 0`, and
`E_ν τ ≤ C (h + log D + 1)³`.

**Formalization Note** The constants are quantified after `k, r` and before the process,
`D`, `ν`. The paper's `C′` of the expectation bound is absorbed into `C` (one constant
serving both bounds). `E_ν τ` is the lower Lebesgue integral of the `ℕ∞`-valued `τ` cast to
`ℝ≥0∞` (`τ = ⊤` contributes `∞`). `log` is the natural logarithm; `T^{1/3}` is `Real.rpow`. -/
theorem lemma_C_1_tail_expectation (k r : ℕ) (hk : k < 2 * r) (hr : r < k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ),
        IsPotentialProcess k r live pot h → ∀ D : ℝ, 1 ≤ D →
          ∀ ν : Measure (ℕ → Fin k), ν ∈ SourceClass k (sStar k r) D →
            (∀ T : ℕ, ν {ω | (T : ℕ∞) < hitTime live ω} ≤
                ENNReal.ofReal (min 1 (C * D * lam k r ^ h *
                  Real.exp (-c * (T : ℝ) ^ ((1 : ℝ) / 3))))) ∧
              ∫⁻ ω, ((hitTime live ω : ℕ∞) : ENNReal) ∂ν ≤
                ENNReal.ofReal (C * ((h : ℝ) + Real.log D + 1) ^ 3) := by sorry

end CorrelatedLocalSearch
