-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_50
-- name    : CubicPermFPRAS.lemma_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:57:35.78811+00:00
-- url     : https://prove2.me/theorems/d6e2a77b-58ad-476c-9b5e-ab92af64b924
-- title:
--   Lemma 50, p.55 — annealing schedule: length $O(\Delta\log(2H_{\max}))$, steps $\delta_i\le1/4$, relative second moment $\le e^{3/4}<64/27$
-- statement:
--   Let $\Omega$ be finite, $H:\Omega\to[0,H_{\max}]$ with $H_{\max}\ge1$, and $0<\beta_{\max}\le\Delta$ with $\Delta\ge1$. Set $\beta_0=0$ and, until $\beta_L=\beta_{\max}$,
--   $$d_i=\min\Big\{\beta_{\max}-\beta_i,\ \tfrac14\max\Big\{\tfrac1{H_{\max}},\tfrac{\beta_i}{\Delta}\Big\}\Big\},\qquad\beta_{i+1}=\beta_i+d_i.$$
--   There is a universal constant $C$ such that the schedule reaches $\beta_{\max}$ after $L\le C\Delta\log(2H_{\max})$ steps, and for every nonempty $S\subseteq\Omega$ with $z_S(0)-z_S(\beta_{\max})\le\Delta$:
--
--   1. $\delta_i=z_S(\beta_i)-z_S(\beta_{i+1})\le1/4$ for every $0\le i<L$;
--   2. for two such families $S,S'$, the ratio $Z_S(\beta_i)/Z_{S'}(\beta_i)$ changes by a factor in $[e^{-1/4},e^{1/4}]\subseteq[3/4,4/3]$ between consecutive temperatures;
--   3. the product $Y=\prod_{i<L}e^{-d_iH(M_i)}$ with independent $M_i\sim\mu_{S,\beta_i}$ has relative second moment $\mathbb E[Y^2]/\mathbb E[Y]^2\le e^{3/4}<64/27$.
--
--   This is the non-adaptive annealing schedule behind the cooling schedule of Lemma 7.
--
--   Differences from the source:
--   - generalization: the conclusions for $S=\mathcal P$ and every $S=\mathcal N(u,v)$ of $K_{n,n}$ → the conclusions for every nonempty $S$ (and every pair $S,S'$) satisfying $z_S(0)-z_S(\beta_{\max})\le\Delta$ in any finite $\Omega$; reason: the schedule does not depend on $S$ and each conclusion uses only the hypothesis on its own families; the source families are instances
--   - encoding: $L=O(\Delta\log(2H_{\max}))$; "until $\beta_L=\beta_{\max}$" → a universal $C>0$ quantified before all data; the schedule reaches $\beta_{\max}$ at the first index $L$ with $\beta_L=\beta_{\max}$; reason: the standard reading of $O(\cdot)$ and of the stopping rule
--   - encoding: relative second moment of $Y$ with independent $M_i$ → $\prod_i\mathbb E[Y_i^2]/(\prod_i\mathbb E[Y_i])^2$ with finite sums; reason: independence factorizes both moments
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 50, p.55 (PDF 57)

import Mathlib
import Definitions.Def_CubicPermFPRAS_coolingSchedule

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 50** (annealing schedule), p.55 (PDF 57), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

Let `H : Ω → [0, H_max]` with `H_max ≥ 1` and `0 < β_max ≤ Δ` with `Δ ≥ 1`. With `β₀ = 0` and
`d_i = min{β_max − β_i, ¼ max{1/H_max, β_i/Δ}}`, the schedule reaches `β_max` after
`L = O(Δ log(2H_max))` steps; for every nonempty `S ⊆ Ω` with `z_S(0) − z_S(β_max) ≤ Δ` each
`δ_i = z_S(β_i) − z_S(β_{i+1})` is at most `1/4`, ratios `Z_S/Z_{S'}` of two such families change by
factors in `[e^{−1/4}, e^{1/4}] ⊆ [3/4, 4/3]` between consecutive temperatures, and the product `Y`
has relative second moment at most `e^{3/4} < 64/27`.

**Formalization Note.** The paper states the hypothesis for `S = P` and every `S = N(u,v)`;
since the schedule does not depend on `S`, the conclusions are stated for every nonempty `S`
satisfying the hypothesis (and for every pair of such `S, S'`). "Until `β_L = β_max`" is the
clause that the schedule reaches `β_max` at index `L`. The relative second moment is
`∏_i E[Y_i²] / (∏_i E[Y_i])²` (independence). -/
theorem lemma_50 : ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [Fintype Ω] (H : Ω → ℝ) (Hmax βmax Δ : ℝ),
      (∀ M, 0 ≤ H M ∧ H M ≤ Hmax) → 1 ≤ Hmax → 0 < βmax → βmax ≤ Δ → 1 ≤ Δ →
      annealBeta Hmax Δ βmax (annealLen Hmax Δ βmax) = βmax ∧
      (annealLen Hmax Δ βmax : ℝ) ≤ C * Δ * Real.log (2 * Hmax) ∧
      (∀ S : Finset Ω, S.Nonempty → zS H S 0 - zS H S βmax ≤ Δ →
        (∀ i < annealLen Hmax Δ βmax,
          zS H S (annealBeta Hmax Δ βmax i) - zS H S (annealBeta Hmax Δ βmax (i + 1)) ≤ 1 / 4) ∧
        annealRelSecondMoment H S Hmax Δ βmax ≤ Real.exp (3 / 4)) ∧
      (∀ S S' : Finset Ω, S.Nonempty → S'.Nonempty →
        zS H S 0 - zS H S βmax ≤ Δ → zS H S' 0 - zS H S' βmax ≤ Δ →
        ∀ i < annealLen Hmax Δ βmax,
          Real.exp (-(1 / 4)) ≤
              (ZS H S (annealBeta Hmax Δ βmax (i + 1)) / ZS H S' (annealBeta Hmax Δ βmax (i + 1))) /
                (ZS H S (annealBeta Hmax Δ βmax i) / ZS H S' (annealBeta Hmax Δ βmax i)) ∧
            (ZS H S (annealBeta Hmax Δ βmax (i + 1)) / ZS H S' (annealBeta Hmax Δ βmax (i + 1))) /
                (ZS H S (annealBeta Hmax Δ βmax i) / ZS H S' (annealBeta Hmax Δ βmax i)) ≤
              Real.exp (1 / 4)) ∧
      (3 / 4 ≤ Real.exp (-(1 / 4)) ∧ Real.exp (1 / 4) ≤ 4 / 3) ∧
      Real.exp (3 / 4) < 64 / 27 := by sorry

end CubicPermFPRAS
