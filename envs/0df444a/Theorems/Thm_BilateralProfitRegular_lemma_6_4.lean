-- Prove2me | Theorems.Thm_BilateralProfitRegular_lemma_6_4
-- name    : BilateralProfitRegular.lemma_6_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:36.693763+00:00
-- url     : https://prove2.me/theorems/e285466f-7085-4cfd-b8d9-34cbe7914dad
-- title:
--   Lemma 6.4 — Initialize regular: scale, $O(\sqrt{\delta/\eta}\log 2T)$ valid candidates, and $O(K\log^2T)$ regret
-- statement:
--   Let $\eta\in(0,1)$, let $K=\lceil1/\eta\rceil\le T$, and let the distributions be independent and regular on $[0,1]$ with strictly positive densities. Consider Algorithm 7 (Initialize regular) run until it finishes, without stopping at $T$. With probability at least $1-1/T$ one of the following holds:
--
--   1. it returns "no trigger" and $\mu^\star\le C/K$; or
--   2. it returns a scale $\delta$ and $N\le C\sqrt{\delta/\eta}\log(2T)$ candidates $(\mathcal K_i,w_i,\theta_i,\widehat P(w_i))$ with $\delta>\eta$ and $\delta\le\mu^\star<6\delta$, such that:
--      - each $\mathcal K_i\subset\mathrm{int}(\mathcal T)$ is compact and convex and contains its root $w_i$;
--      - (i) for every candidate and $|u|\le10^{-3}$, $r_{\lambda_ie^u}\ge0.99\mu^\star$ on $\mathcal K_i$, and some candidate $i^\star$ satisfies $\max_{x\in\mathcal K_{i^\star}}r_{\lambda_{i^\star}e^u}(x)\ge\mu^\star-3\eta$ for $|u|\le10^{-3}\sqrt{\eta/\delta}$;
--      - (ii) for any two points of $\mathcal K_i$ both crosses belong to $\mathcal T$, the trade probabilities of the crosses and of the points lie in $[\widehat P(w_i)/10,10\widehat P(w_i)]$, $\delta\le\widehat P(w_i)\le1$, and $\delta/(q-p)\le10\widehat P(w_i)$ on $\mathcal K_i$;
--      - the run's regret $\sum_t(\mu^\star-\mu(a_t))$ is at most $CK\log^2T$.
--
--   Here $C$ is a universal constant, and the statement holds for every processing order of step 4. The proof gives $\mu^\star<6\cdot2^{16}/K$ in the no-trigger case.
--
--   Differences from the source:
--   - generalization: "Process retained pairs in a fixed order" (Algorithm 7, step 4) → the statement holds for every processing order (a duplicate-free list of $\mathcal A$); reason: it specializes to whichever fixed order the algorithm uses
--   - reading: Algorithm 4's bisection and "the midpoint of the first recursive split separating $i,j$"; step 4's choice of root when several pass; $\widehat P(i/K,j/K)$ for $i>j$ → $\{m,\dots,M\}$ splits into $\{m,\dots,k_I\}$ and $\{k_I+1,\dots,M\}$; the earliest created root that passes; $\widehat P=0$ for $i>j$; reason: the paper does not spell these out; the bisection is the reading under which (48) uses sampled pairs $(i,k),(k,j),(k,k)$ (p.60); pairs with $i>j$ are used only after the $\mathcal T$ test
--   - encoding: "with probability at least $1-1/T$" over fresh trade bits; "$\mu^\star=O(1/K)$", "$N=O(\cdot)$", "$O(K\log^2(T))$ regret" → the measure of the failure event is at most $1/T$; one universal constant $C$ chosen before $T,\eta$, the environment and the order; reason: trade bits realized from i.i.d. uniforms with the same law; the complement form is the stronger one; the constants are universal in the proof
--   - encoding: "initialization incurs $O(K\log^2(T))$ regret" → $\sum$ over all rounds of the full run of $\mu^\star-\mu(a_t)$, on the good triggered event; reason: the rounds of the run are a function of its transcript; regret of fixed posted pairs is the sum of their gaps
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.4, p.40 (PDF 42); proof App. A.6, pp.61–65 (PDF 63–67)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_InitRegular

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- **Lemma 6.4 (Initialization)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256
e91e8127…), p.40 (PDF 42); proof App. A.6, pp.61–65 (PDF 63–67). Consider Initialize regular
(Algorithm 7) running until it is finished, without stopping at `T`. With probability at least
`1 − 1/T` it either returns "no trigger", with `µ⋆ = O(1/K)`, or returns a scale `δ > η` with
`δ ≤ µ⋆ < 6δ` and a list of `N = O(√(δ/η) log(2T))` candidates `(𝒦_i, w_i, θ_i, P̂(w_i))`,
each `𝒦_i ⊂ int(𝒯)` compact and convex containing its root `w_i`, satisfying (i) the
auxiliary-profit guarantees (with some candidate `i⋆` near-optimal) and (ii) the crossed-query
bounds (`Candidate.Valid`, `Candidate.NearOpt`, `InitGuarantee`); on such a valid triggered
transcript, initialization incurs `O(K log²(T))` regret.

**Formalization Note.** The run is Algorithm 7 to completion (`initRegular`), driven by i.i.d.
uniforms that realize fresh trade bits; the probability is over them. The failure event's measure
is bounded (the complement form, which is the stronger one for a possibly non-measurable event).
`O(·)` is one universal constant `C` chosen before `T`, `η`, the environment and the processing
order of step 4; the statement holds for every order. `K = ⌈1/η⌉ ≤ T` is the algorithm's input
condition. The regret is `∑ (µ⋆ − µ(a_t))` over all rounds of the full run. The proof gives
`µ⋆ < 6·2^16/K` in the no-trigger case. -/
theorem lemma_6_4 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ (E : Environment), RegularUnit E →
      ∀ ord : List (ℕ × ℕ), IsOrder (gridK η) ord →
        initCoinLaw {U |
          ¬ (match initRegular T η ord (P E) U with
            | none => muStar E ≤ C / gridK η
            | some (δ, cs) =>
                InitGuarantee E η δ cs ∧
                (cs.length : ℝ) ≤ C * Real.sqrt (δ / η) * Real.log (2 * T) ∧
                initRegret E T η U ≤ C * gridK η * Real.log T ^ 2)} ≤
          ENNReal.ofReal (1 / T) := by sorry

end BilateralProfitRegular
