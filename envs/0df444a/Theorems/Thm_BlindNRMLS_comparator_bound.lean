-- Prove2me | Theorems.Thm_BlindNRMLS_comparator_bound
-- name    : BlindNRMLS.comparator_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:00.299947+00:00
-- url     : https://prove2.me/theorems/ba208edf-dbc3-4a53-81b0-3a4185925261
-- title:
--   (EC.46), p.ec55 — $J^{\mathrm{DLP}_{\mu'}}-\mathrm{Rev}(\pi^*[s])\le4\sqrt{T\log T}+1$ for a single-arm optimum
-- statement:
--   Let $b\in(0,\infty)^d$, $T\ge2$, $d+1\le K\le T$, $n\ge d+1$ and $\mu_1,\mu_2\in[-\frac12,\frac12]^K$. Suppose that some arm $k'$ has $\mu_{2,k'}=0$ and $J^{\mathrm{DLP}_\mu}=(\frac12+\mu_{1,k'})T$. Then for every switching budget $s$,
--   $$
--   J^{\mathrm{DLP}_\mu}-\sup_{\pi\in\Pi_{Q_\mu}[s]}\mathrm{Rev}_{Q_\mu}(\pi)\le4\sqrt{T\log T}+1 .
--   $$
--   It lets the lower bound replace the clairvoyant $s$-switch benchmark by the LP value.
--
--   Differences from the source:
--   - generalization: the single instance I_µ′ of Case 1 with µ′_{2,k′}=0 and µ′_{1,k′}=∆₁ → any µ with µ_{2,k′}=0 and J^DLP=(½+µ_{1,k′})T; reason: these are the only properties the bound uses, and all three uses in the proof are covered
--   - encoding: the proof's standing T ≥ 2K → 2 ≤ T and d+1 ≤ K ≤ T; reason: the display is stated in that proof, whose +1 absorbs d/T
--   - reading: the model does not say whether the demands of different products in one period are independent → the joint law under arm k is the product of the marginal laws on [0,1]; reason: p.2 says demand is independent, p.20 has q determine a Bernoulli instance, and the clean event and Lemma EC.6 need it
--   - reading: selling stops when the cumulative demand of a resource exceeds its inventory → a period earns revenue iff consumption through it is within B; reason: the display of the effective horizon on p.ec22 fixes this; the violating period earns nothing
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
--   - generalization: clairvoyant policies have the signature R^d × [s] × [T] → Δ([K]) → clairvoyant policies are all history-dependent policies with at most s switches a.s. under that Q; reason: this class contains the page's, and the signature omits the last action, which a switch-limited policy must know
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, proof of Theorem 4, Case 1, (EC.46), p.ec55; x_{k′}=T, p.ec54

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- (EC.46): on an instance `I_µ'` with `µ'_{2,k'} = 0` whose DLP value is `(1/2 + µ'_{1,k'}) T`, the
optimal `s`-switch clairvoyant revenue for any `s` is within `4√(T log T) + 1` of the DLP value.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, proof of Theorem 4, Case 1, p.ec55.

**Formalization Note.** The page's single instance is stated as a family: only arm `k'` needs `µ_2 = 0`,
and the hypothesis on `J` is the page's `x_{k'} = T` (p.ec54). `K ≤ T` and `d + 1 ≤ K` give `d ≤ T`, which
the `+ 1` absorbs; they hold on the proof's standing `T ≥ 2K`. -/
theorem comparator_bound (T d n K : ℕ) (b : Fin d → ℝ) (hb : ∀ i, 0 ≤ b i) (hb_pos : ∀ i, 0 < b i)
    (hT : 2 ≤ T) (hdK : d + 1 ≤ K) (hKT : K ≤ T) (hdn : d + 1 ≤ n) (μ₁ μ₂ : Fin K → ℝ)
    (hμ₁ : ∀ k, |μ₁ k| ≤ 1 / 2) (hμ₂ : ∀ k, |μ₂ k| ≤ 1 / 2) (k' : Fin K) (hk' : μ₂ k' = 0)
    (hJ : J (hardProblem T b hb n K) (hardLaw d μ₁ μ₂) = (1 / 2 + μ₁ k') * (T : ℝ)) (s : ℕ) :
    J (hardProblem T b hb n K) (hardLaw d μ₁ μ₂) -
        optRev (hardProblem T b hb n K) (hardLaw d μ₁ μ₂) s ≤
      4 * Real.sqrt ((T : ℝ) * Real.log T) + 1 := by sorry

end BlindNRMLS
