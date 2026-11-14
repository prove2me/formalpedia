-- Prove2me | Theorems.Thm_BilateralProfitMHR_lemma_3_3
-- name    : BilateralProfitMHR.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:19.941422+00:00
-- url     : https://prove2.me/theorems/2ac92fe0-33ef-46ac-b0d5-63615707af0c
-- title:
--   Lemma 3.3 — the filtering procedure, qualitative form (constants $0<c<C$, regret $\tilde O(K)$)
-- statement:
--   There exist constants $0<c<C$ and $C'$ such that the following holds for all $2\le K\le T$ and every pair of independent MHR seller and buyer laws with densities strictly positive on $[0,1]$. With probability at least $1-1/T$, the filtering procedure (Initialize mhr) either
--
--   1. does not trigger and $\mu^\star\le C/K$, or
--   2. returns a scale $\varepsilon_{h^\star}=2^{-h^\star}\ge1/K$ and a convex body $\mathcal K\subseteq\operatorname{int}(\mathcal T)$ (nonempty, compact, convex) such that
--      - (i) every price $(p,q)\in\mathcal K$ has $\mu(p,q)\ge c\,\varepsilon_{h^\star}$;
--      - (ii) $\varepsilon_{h^\star}\le\mu^\star\le C\,\varepsilon_{h^\star}$;
--      - (iii) $\mathcal K$ contains every maximizer of $\mu$ over $G_K\cap\mathcal T$, and $\mu^\star\le\max_{(p,q)\in\mathcal K}\mu(p,q)+C/K$;
--
--      and the regret incurred during filtering, $\sum(\mu^\star-\mu(p_t,q_t))$ over the probing rounds, is at most $C'K\log^2(2T)$.
--
--   This is the overview's summary of Lemma 5.3.
--
--   Differences from the source:
--   - reading: "with high probability" → with probability at least $1-1/T$ over the probing valuations; reason: the strength at which Lemma 5.3 and Proposition 5.4 prove it
--   - reading: "the regret incurred during filtering is $\tilde O(K)$" → at most $C'K\log^2(2T)$ for a universal $C'$; reason: $\tilde O$ hides logarithmic factors in $T$; the bound proved is $6CK\log^2(2T)$ (display after (31), p.34)
--   - reading: "the filtering procedure" → Initialize mhr (Algorithm 4) with $2\le K\le T$, on independent MHR laws with strictly positive densities on $[0,1]$, with the bisection reading of Proposition 5.4; reason: the paper refers to Lemma 5.3 for the exact statement, whose standing hypotheses these are
--   - encoding: "convex body"; "$\max_{(p,q)\in\mathcal K}\mu$" → nonempty compact convex set (possibly lower-dimensional); a maximizer in $\mathcal K$ exists; reason: Lemma 5.3's "nonempty, compact, convex"; the maximum is attained
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 3.3, p.11 (PDF 13); exact form Lemma 5.3, pp.32–34 (PDF 34–36)

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

/-- **Lemma 3.3**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), p.11
(PDF 13): there exist constants `0 < c < C` such that, with high probability, the filtering
procedure either does not trigger and `µ⋆ ≤ C/K`, or returns `ε_{h⋆} = 2^{−h⋆} ≥ 1/K` and a
convex body `𝒦 ⊆ int(𝒯)` satisfying (i) `µ(p, q) ≥ c·ε_{h⋆}` on `𝒦`; (ii)
`ε_{h⋆} ≤ µ⋆ ≤ C·ε_{h⋆}`; (iii) `𝒦` contains every maximizer of `µ` over `G_K ∩ 𝒯`, and therefore
`µ⋆ ≤ max_{𝒦} µ + C/K`. On the same high-probability event, if the procedure triggers, the regret
incurred during filtering is `Õ(K)`.

**Formalization Note.** The filtering procedure is Initialize mhr (Algorithm 4) with
`2 ≤ K ≤ T`; the paper refers to Lemma 5.3 for the exact statement. "With high probability" is
read as probability at least `1 − 1/T` (Lemma 5.3, Proposition 5.4) over the probing valuations;
`Õ(K)` as `C′·K·log²(2T)` for a universal `C′` (the display after (31), p.34); the regret during
filtering is the realized `∑ (µ⋆ − µ(p_t, q_t))` of the probing rounds. A convex body is a
nonempty compact convex set (possibly lower-dimensional). The max over `𝒦` is stated with
attainment. All constants are universal: chosen before `T`, `K` and the distributions
(independent, positive densities on `[0, 1]`, both MHR). -/
theorem lemma_3_3 :
    ∃ c C C' : ℝ, 0 < c ∧ c < C ∧ ∀ T K : ℕ, 2 ≤ K → K ≤ T →
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none ∧ muStar E.prior ≤ C / K) ∨
            ∃ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) ∧ 1 / (K : ℝ) ≤ delta h ∧
              R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT ∧
              (∀ x ∈ R, c * delta h ≤ muP E.prior x) ∧
              (delta h ≤ muStar E.prior ∧ muStar E.prior ≤ C * delta h) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior ≤ muP E.prior x + C / K) ∧
              filterRegret K T E.prior ω ≤ C' * K * Real.log (2 * T) ^ 2 := by sorry

end BilateralProfitMHR
