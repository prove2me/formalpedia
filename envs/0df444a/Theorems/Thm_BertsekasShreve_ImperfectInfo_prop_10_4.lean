-- Prove2me | Theorems.Thm_BertsekasShreve_ImperfectInfo_prop_10_4
-- name    : BertsekasShreve.ImperfectInfo.prop_10_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:42:06.865984+00:00
-- url     : https://prove2.me/theorems/94deb918-2fbc-4a4c-9461-ff501e70e853
-- title:
--   Proposition 10.4 — ε-optimal nonrandomized (ISI) policies that depend on $i_k$ only through $\eta_k(p;i_k)$
-- statement:
--   Let an (ISI) model with finite horizon $N$ and a statistic $(\eta_0,\dots,\eta_{N-1})$ sufficient for control be given, and assume $(F^+,\hat F^+)$ or $(F^-,\hat F^-)$. Then for every $\varepsilon>0$:
--
--   1. there is an $\varepsilon$-optimal nonrandomized policy for (ISI) which depends on $i_k=(z_0,u_0,\dots,u_{k-1},z_k)$ only through $\eta_k(p;i_k)$, i.e. of the form
--   $$\pi=\big(\mu_0[p;\eta_0(p;i_0)],\dots,\mu_{N-1}[p;\eta_{N-1}(p;i_{N-1})]\big);$$
--   2. under $(F^+,\hat F^+)$, such a policy can be chosen of the simpler form
--   $$\hat\pi=\big(\hat\mu_0[\eta_0(p;i_0)],\dots,\hat\mu_{N-1}[\eta_{N-1}(p;i_{N-1})]\big).$$
--
--   A nonrandomized policy assigns at each stage a single control, so the kernels are point masses $\delta_{\mu_k[p;\eta_k(p;i_k)]}$; being a policy includes universal measurability and the control constraints.
--
--   **Formalization Note** Finite-horizon cases only; the book's second part also covers $(P,\hat P)$ and $(D,\hat D)$, which are out of scope.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 257, Proposition 10.4 (Eqs. (44)–(45) of Chapter 10)

import Mathlib
import Definitions.Def_BertsekasShreve_ImperfectInfo_SufficientStatistic

open MeasureTheory ProbabilityTheory

namespace BertsekasShreve.ImperfectInfo

/-- Proposition 10.4 (p. 257), finite horizon, under (F⁺, F̂⁺) or (F⁻, F̂⁻). -/
theorem prop_10_4 {S C Z : Type}
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace C] [MeasurableSpace C] [BorelSpace C]
    [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (M : ISIModel S C Z) {Y : ℕ → Type} [∀ k, TopologicalSpace (Y k)] [∀ k, MeasurableSpace (Y k)]
    (σ : SuffStat M Y)
    (hF : (M.Fplus ∧ σ.FhatPlus) ∨ (M.Fminus ∧ σ.FhatMinus))
    (ε : ℝ) (hε : 0 < ε) :
    (∃ f : (k : ℕ) → ProbabilityMeasure S × Y k → C,
      M.IsEpsOptimal
        (fun k pi => ⟨Measure.dirac (f k (pi.1, σ.η k pi)), inferInstance⟩) ε) ∧
    (M.Fplus ∧ σ.FhatPlus →
      ∃ f : (k : ℕ) → Y k → C,
        M.IsEpsOptimal (fun k pi => ⟨Measure.dirac (f k (σ.η k pi)), inferInstance⟩) ε) := by sorry

end BertsekasShreve.ImperfectInfo
