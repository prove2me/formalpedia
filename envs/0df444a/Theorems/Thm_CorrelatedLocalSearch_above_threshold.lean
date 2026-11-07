-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_above_threshold
-- name    : CorrelatedLocalSearch.above_threshold
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:44.955291+00:00
-- url     : https://prove2.me/theorems/ba629927-426a-4c42-992c-82b6009e21ad
-- title:
--   Proof of Theorem 4.1 — above the threshold: $M_T\le\lambda^hk^{-\delta T}$, $\mathbb P_\nu\{\tau>T\}\le D\lambda^hk^{-\delta T}$, $\mathbb E_\nu\tau\le CL/\delta$
-- statement:
--   Fix integers $k/2<r<k$. There is a constant $C>0$, depending only on $k$ and $r$, such that for every process satisfying the integer-potential hypotheses of Lemma C.1 with initial potential $h$, every $s\in[s_*,1]$ with $\delta=s-s_*$, every $D\ge1$ and every $\nu\in\mathcal Q_{s,D}$:
--
--   1. for every $T\ge0$, with $d(w)$ the potential of $w$,
--   $$
--   M_T=\sum_{|w|=T,\ w\text{ live}}k^{-sT}\lambda^{d(w)}\ \le\ \lambda^h k^{-\delta T};
--   $$
--   2. for every $T\ge0$, $\ \mathbb P_\nu\{\tau>T\}\le D\lambda^h k^{-\delta T}$;
--   3. if $\delta>0$, then with $L=h+\log D+1$,
--   $$
--   \mathbb E_\nu\tau\ \le\ C\,\frac{L}{\delta}.
--   $$
--
--   This is the exponential-tail half of (9) and the $L/\delta$ half of (10); the paper notes that the weighted-tree argument applies to the general potential of Lemma C.1.
--
--   **Formalization Note** "Live length-$T$ histories" are the surviving words of length $T$, written `List.ofFn v`; $k^{-\delta T}$ is a real power.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - encoding: a deterministic process with live histories, a potential and a stopping time τ → a liveness predicate `live` and a potential `pot` on words; a history is live in the paper's sense when all its prefixes satisfy `live` (`Surv`); τ = hitTime live ∈ ℕ∞, ⊤ if it never stops; reason: every deterministic process driven by the tape is described this way, and conversely
--   - encoding: E_ν τ → lower Lebesgue integral ∫⁻ of τ cast from ℕ∞ to ℝ≥0∞; reason: τ is measurable (each {τ > T} is a finite union of cylinders), so this is the expectation, with value ∞ when ν{τ = ∞} > 0
--   - encoding: log D (base not fixed) → natural logarithm Real.log; reason: another fixed base only rescales C
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_IsPotentialProcess

set_option autoImplicit false

open Classical

namespace CorrelatedLocalSearch

open MeasureTheory

/-- The bound above the threshold (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Theorem 4.1, p.23, for the general
potential of Lemma C.1: "This weighted-tree argument also applies to the general potential in
Lemma C.1"): for `k/2 < r < k` there is `C > 0` depending only on `k, r` such that, for every
process satisfying the hypotheses of Lemma C.1 with initial potential `h`, every
`s ∈ [s∗, 1]` with `δ = s − s∗`, every `D ≥ 1`, `ν ∈ Q_{s,D}` and every `T`,
1. `M_T = Σ_{|w| = T, w live} k^{−sT} λ^{d(w)} ≤ λ^h k^{−δT}`;
2. `P_ν{τ > T} ≤ D λ^h k^{−δT}`;
3. if `δ > 0`, `E_ν τ ≤ C L/δ` with `L = h + log D + 1`.

**Formalization Note** "Live length-`T` histories" are the surviving words of length `T`
(`List.ofFn v`, `v : Fin T → Fin k`). `E_ν τ` is the lower Lebesgue integral of the
`ℕ∞`-valued `τ`; `log` is natural; `k^{−δT}` is `Real.rpow`. -/
theorem above_threshold (k r : ℕ) (hk : k < 2 * r) (hr : r < k) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (live : List (Fin k) → Prop) (pot : List (Fin k) → ℕ) (h : ℕ),
        IsPotentialProcess k r live pot h → ∀ s : ℝ, sStar k r ≤ s → s ≤ 1 →
          ∀ D : ℝ, 1 ≤ D → ∀ ν : Measure (ℕ → Fin k), ν ∈ SourceClass k s D →
            (∀ T : ℕ, ∑ v : Fin T → Fin k,
                (if Surv live (List.ofFn v) then
                  (k : ℝ) ^ (-(s * T)) * lam k r ^ pot (List.ofFn v) else 0) ≤
                lam k r ^ h * (k : ℝ) ^ (-((s - sStar k r) * T))) ∧
            (∀ T : ℕ, ν {ω | (T : ℕ∞) < hitTime live ω} ≤
                ENNReal.ofReal (D * lam k r ^ h * (k : ℝ) ^ (-((s - sStar k r) * T)))) ∧
            (0 < s - sStar k r →
              ∫⁻ ω, ((hitTime live ω : ℕ∞) : ENNReal) ∂ν ≤
                ENNReal.ofReal (C * ((h : ℝ) + Real.log D + 1) / (s - sStar k r))) := by sorry

end CorrelatedLocalSearch
