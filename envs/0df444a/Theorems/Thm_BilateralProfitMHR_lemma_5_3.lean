-- Prove2me | Theorems.Thm_BilateralProfitMHR_lemma_5_3
-- name    : BilateralProfitMHR.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:02.986213+00:00
-- url     : https://prove2.me/theorems/cdbbed68-efc6-44d9-886a-c4ccc7ef00f4
-- title:
--   Lemma 5.3 — Initialize mhr returns a safe convex region; $O(\sqrt T\log T)$ regret for $K=\lfloor c_0\sqrt T/\log(2T)\rfloor$
-- statement:
--   Let $2\le K\le T$, and let the seller and buyer laws be independent, with densities strictly positive on $[0,1]$, both MHR. Write $\mu^\star=\sup_{[0,1]^2}\mu$.
--
--   Whenever Initialize mhr triggers, the returned region $\mathcal K$ is nonempty, compact, convex and contained in $\{0<p<q<1\}$. With probability at least $1-1/T$ the following hold:
--
--   1. if the procedure returns "no trigger", then $\mu^\star<6/K$; otherwise its returned scale satisfies $\delta\le\mu^\star<6\delta$;
--   2. every returned region satisfies $P(p,q)\ge\mu(p,q)\ge\delta/2$ for all $(p,q)\in\mathcal K$;
--   3. every returned region contains all maximizers of $\mu$ over the triangle grid, and
--   $$\mu^\star_{\mathcal K}=\max_{(p,q)\in\mathcal K}\mu(p,q)\ge\mu^\star-\frac2K .$$
--
--   Moreover, there are universal constants $c_0\in(0,1/2]$ and $C$ such that, with
--   $$K=\Big\lfloor\frac{c_0\sqrt T}{\log(2T)}\Big\rfloor\tag{28}$$
--   and whenever this $K$ is at least $2$, Initialize mhr uses at most $T$ rounds on every history and its expected regret $\mathbb E\big[\sum(\mu^\star-\mu(p_t,q_t))\big]$ over its rounds is at most $C\sqrt T\log T$; if it returns "no trigger", posting $(0,0)$ in all remaining rounds keeps the expected regret over the whole horizon below the same bound.
--
--   The lemma reduces the problem to a convex one on a region where the loss $-\log\mu$ has a bounded range, at a cost of $O(\sqrt T\log T)$ regret.
--
--   Differences from the source:
--   - reading: "the first recursive split separating $i$ and $j$" → the midpoint $k$ of the smallest bisection interval containing both, so $i\le k<j$; reason: the bisection rule is not spelled out; this is the reading under which the proof of Proposition 5.4 holds as printed (p.60)
--   - encoding: posting each pair for $N$ fresh rounds → an array of independent samples indexed by (scale, grid pair, repetition); and "with probability at least $1-1/T$" → a measurable event of that probability; reason: the run at a scale reads only that scale's samples, so every event has the same probability
--   - encoding: $\mu^\star_{\mathcal K}=\max_{\mathcal K}\mu\ge\mu^\star-2/K$ → there is a maximizer $x$ of $\mu$ on $\mathcal K$ with $\mu(x)\ge\mu^\star-2/K$; reason: the maximum is attained, as "max" says
--   - reading: "for a universal constant $c_0$, choosing $K$ as in (28) ensures … $O(\sqrt T\log T)$ expected regret" → there are $c_0\in(0,1/2]$ and $C$ such that for every $T$ whose $K$ from (28) is at least $2$ the round bound and the expected-regret bound $C\sqrt T\log T$ hold; reason: the lemma's standing hypothesis is $2\le K\le T$, and $K\le T$ follows from $c_0\le1/2$ (Algorithm 6 fixes $c_0\in(0,1/2]$); $O(\cdot)$ is a universal constant
--   - encoding: "incurs … expected regret" → the expectation of $\sum(\mu^\star-\mu(p_t,q_t))$ over its rounds (plus $(T-\text{rounds})\mu^\star$ after "no trigger", posting $(0,0)$ earns $0$), as a $[0,\infty]$-valued integral; reason: the paper's regret in the form (36); the summands are nonnegative
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 5.3 and Equation (28), pp.32–33 (PDF 34–35); proof pp.33–34 (PDF 35–36)

import Mathlib
import Definitions.Def_BilateralProfitMHR_InitializeMHR

namespace BilateralProfitMHR

open MeasureTheory BilateralProfit MechanismDesign.BilateralTrade
open scoped ENNReal

/-- **Lemma 5.3 (Initialize mhr guarantees)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), pp.32–33 (PDF 34–35); proof pp.33–34 (PDF 35–36).

Let `2 ≤ K ≤ T`. Whenever Initialize mhr triggers, the returned region `𝒦` is nonempty, compact,
convex, and contained in the interior of `𝒯`. With probability at least `1 − 1/T`:
(i) if it returns "no trigger" then `µ⋆ < 6/K`; otherwise the returned scale satisfies
`δ ≤ µ⋆ < 6δ`; (ii) every returned `𝒦` satisfies `P(p, q) ≥ µ(p, q) ≥ δ/2` on `𝒦`; (iii) every
returned `𝒦` contains all grid maximizers, and `µ⋆_𝒦 = max_{𝒦} µ ≥ µ⋆ − 2/K`.
Moreover, for a universal constant `c₀`, choosing `K = ⌊c₀ √T / log(2T)⌋` (28) ensures that
Initialize mhr uses at most `T` rounds on every history and incurs `O(√T log T)` expected
regret; if it returns "no trigger", posting `(0, 0)` thereafter gives the same regret bound over
the entire horizon.

**Formalization Note.** Distributions: independent, densities strictly positive on `[0, 1]`,
both MHR. `δ_h = 2^{−h}` is the returned scale of `initOut = some (h, 𝒦)`. "Grid maximizers" are
the maximizers of `µ` over the triangle grid `G_K = 𝒜`. The max over `𝒦` is stated with
attainment. The probability is over the probing valuations (`initLaw`), as a measurable event.
The "Moreover" clause: `∃ c₀ ∈ (0, 1/2]` and `C`, and for every `T` whose `K` of (28) satisfies
the lemma's standing `2 ≤ K` (then `K ≤ T`), every run uses at most `T` rounds and the expected
regret of the probing rounds, `E[∑ (µ⋆ − µ(p_t, q_t))]`, is at most `C √T log T`, also after
adding, on "no trigger", the regret `(T − rounds)·µ⋆` of posting `(0, 0)` (whose profit is `0`)
in the remaining rounds. Expectations are in `ℝ≥0∞` of nonnegative quantities. -/
theorem lemma_5_3 :
    (∀ T K : ℕ, 2 ≤ K → K ≤ T →
      (∀ (ω : Samples K T) (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
          R.Nonempty ∧ IsCompact R ∧ Convex ℝ R ∧ R ⊆ intT) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∃ G : Set (Samples K T), MeasurableSet G ∧ 1 - (T : ℝ≥0∞)⁻¹ ≤ initLaw K T E.prior G ∧
          ∀ ω ∈ G,
            (initOut K T ω = none → muStar E.prior < 6 / K) ∧
            ∀ (h : ℕ) (R : Set (ℝ × ℝ)), initOut K T ω = some (h, R) →
              (delta h ≤ muStar E.prior ∧ muStar E.prior < 6 * delta h) ∧
              (∀ x ∈ R, delta h / 2 ≤ muP E.prior x ∧ muP E.prior x ≤ Ptrade E.prior x) ∧
              (∀ e : Act K, IsGridMax K E.prior e → pt K e.1 ∈ R) ∧
              (∃ x ∈ R, (∀ y ∈ R, muP E.prior y ≤ muP E.prior x) ∧
                muStar E.prior - 2 / K ≤ muP E.prior x)) ∧
    (∃ c0 C : ℝ, 0 < c0 ∧ c0 ≤ 1 / 2 ∧ ∀ T : ℕ, 2 ≤ Kpar c0 T →
      (∀ ω : Samples (Kpar c0 T) T, initRounds (Kpar c0 T) T ω ≤ T) ∧
      ∀ E : Environment, UnitSupport E → IsMHR E →
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T) ∧
        ∫⁻ ω, ENNReal.ofReal (filterRegret (Kpar c0 T) T E.prior ω +
              if initOut (Kpar c0 T) T ω = none then
                ((T - initRounds (Kpar c0 T) T ω : ℕ) : ℝ) * muStar E.prior
              else 0)
            ∂(initLaw (Kpar c0 T) T E.prior) ≤
          ENNReal.ofReal (C * Real.sqrt T * Real.log T)) := by sorry

end BilateralProfitMHR
