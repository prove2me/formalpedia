-- Prove2me | Theorems.Thm_AdaDiscRL_theorem_F_3
-- name    : AdaDiscRL.theorem_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:01.454001+00:00
-- url     : https://prove2.me/theorems/396369cf-347c-40ba-85d0-081d0c70ac53
-- title:
--   Theorem F.3 — metric-specific regret bound (first display)
-- statement:
--   There are absolute constants $c,a>0$ such that, with $C_L=aL$, $L=1+L_r+L_V+L_VL_T$, and $\mathrm{Conf}=\widetilde C/n^\alpha$ ($\widetilde C=4\sqrt{H^3\iota}$, $\alpha=\tfrac12$ for AdaQL; $\widetilde C=4L_Vc\sqrt\iota$, $\alpha=\tfrac12$ or $1/d_{\mathcal S}$ for AdaMB), for a run of AdaQL under Assumption 1, or of AdaMB (bonus constant $c$, $L_V>0$) under Assumptions 1 and 2, with probability at least $1-3\delta$,
--   $$
--   \mathrm{Regret}(K)\le12\sqrt{2H^3K\iota}+6H^2\mathbb 1[\mathrm{AdaQL}]+\sum_{h=1}^H6C_L\inf_{r_0>0}\Big(4Kr_0+\frac{\widetilde C^{1/\alpha}}{1-\alpha}\sum_{r\ge r_0}N_r(Z^r_h)\frac{1}{r^{1/\alpha-1}}\Big),
--   $$
--   where $\iota=\log(2HK^2/\delta)$, $r$ runs over the dyadic radii $2^{-\ell}$, and $Z^r_h$ is the near-optimal set with constant $C_L$.
--
--   The bound depends on the instance only through the packing numbers of the near-optimal sets; tuning $r_0$ per step yields Theorem 4.1.
--
--   **Formalization Note** The right side is computed in $[0,\infty]$ (a packing number may be infinite) and the regret enters through `ENNReal.ofReal`.
--
--   Differences from the source:
--   - reading: C_L a constant depending linearly on the Lipschitz constants → C_L = a L with a universal a > 0, also in Z_h^r; reason: reading R2
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - encoding: real-valued bound with N_r possibly infinite → ENNReal.ofReal(Regret) ≤ the right side computed in ℝ≥0∞; reason: packing numbers live in ℕ ∪ {∞}; the regret is nonnegative
--   - encoding: Σ_{r ≥ r₀} over radii of the partition → Σ over ℓ ∈ ℕ with 2^{−ℓ} ≥ r₀; reason: the radii of the hierarchical partition are 2^{−ℓ}
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Theorem F.3, first display, p.51

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_regret
import Definitions.Def_AdaDiscRL_nearOptSet
import Definitions.Def_AdaDiscRL_packingNum
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Theorem F.3 (Final Regret Bound), first display** (arXiv:2110.15843v3, p.51). There are absolute
constants `c, a > 0` such that, with `C_L = a L`, `L = 1 + L_r + L_V + L_V L_T`, writing
`Conf = C̃/n^α` (AdaQL: `C̃ = 4√(H³ log(2HK²/δ))`, `α = 1/2`; AdaMB: `C̃ = 4 L_V c √(log(2HK²/δ))`,
`α = 1/2` if `d_S ≤ 2`, `α = 1/d_S` if `d_S > 2`), for a run of AdaQL under Assumption 1, or of AdaMB
(constant `c`) under Assumptions 1 and 2 with `L_V > 0`, with probability at least `1 − 3δ`,
`Regret(K) ≤ 12√(2H³K log(2HK²/δ)) + 6H² 1[AdaQL] + Σ_{h=1}^H 6 C_L inf_{r₀>0} (4K r₀ +
(C̃^{1/α}/(1 − α)) Σ_{r ≥ r₀} N_r(Z_h^r) / r^{1/α−1})`,
where `r` runs over the dyadic radii `2^{−ℓ}`, `ℓ ∈ ℕ`, and `Z_h^r` is the near-optimal set with
constant `C_L`.

**Formalization Note.** The right side is computed in `ℝ≥0∞` (a packing number may be `⊤`), and the
regret enters as `ENNReal.ofReal`. The "Moreover" display of F.3 is not formalized (it is superseded by
the corrected Theorem 4.1). -/
theorem theorem_F_3 : ∃ c a : ℝ, 0 < c ∧ 0 < a ∧
    ∀ {S A ι : Type} [MetricSpace S] [CompactSpace S] [Nonempty S] [MeasurableSpace S]
    [BorelSpace S] [MetricSpace A] [CompactSpace A] [Nonempty A] [MeasurableSpace A]
    [BorelSpace A]
    (D : S × A → S × A → ℝ) {H : ℕ} (prm : AdaParams H)
    (P : HierPartition S A ι D prm.dS prm.K) (choose : Finset ι → (ι → ℝ) → ι)
    (hD : IsAdmissibleMetric D) (hH : 1 ≤ H) (hK : 1 ≤ prm.K) (hδ0 : 0 < prm.δ) (hδ1 : prm.δ < 1)
    (hLr : 0 ≤ prm.Lr) (hLV : 0 ≤ prm.LV) (hLT : 0 ≤ prm.LT)
    (hv0 : ∀ h : Fin H, (H : ℝ) - h ≤ prm.v0 h ∧ prm.v0 h ≤ H)
    (hchoose : IsArgmaxRule choose)
    (M : EpisodicMDP S A H) (play : ι → Kernel S A)
    (hplay : ∀ B, IsMarkovKernel (play B))
    (hplay_supp : ∀ B x, x ∈ P.sCell B → play B x (P.aCell B)ᶜ = 0)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (traj : Ω → ℕ → EpData S A H),
    (Assumption1 M D prm.LV →
      IsRun M P choose play (statesQL P prm choose) prm.K μ traj →
      1 - 3 * prm.δ ≤ (μ {ω |
        ENNReal.ofReal (regret M P choose play (statesQL P prm choose) prm.K (traj ω)) ≤
          ENNReal.ofReal (12 * Real.sqrt (2 * (H : ℝ) ^ 3 * prm.K * prm.iota) + 6 * (H : ℝ) ^ 2) +
          ∑ h : Fin H, ENNReal.ofReal (6 * (a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT))) *
            ⨅ r₀ : {r : ℝ // 0 < r},
              (ENNReal.ofReal (4 * prm.K * r₀.val) +
                ENNReal.ofReal ((4 * Real.sqrt ((H : ℝ) ^ 3 * prm.iota)) ^ ((2 : ℝ)) / (1 - 1 / ((2 : ℝ)))) *
                  ∑' ℓ : ℕ, if r₀.val ≤ (2 : ℝ) ^ (-(ℓ : ℤ)) then
                    ((packingNum D ((2 : ℝ) ^ (-(ℓ : ℤ)))
                        (nearOptSet M (a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT)) h ((2 : ℝ) ^ (-(ℓ : ℤ)))) : ℕ∞) : ENNReal) *
                      ENNReal.ofReal (((2 : ℝ) ^ (-(ℓ : ℤ))) ^ (-(((2 : ℝ)) - 1)))
                  else 0)}).toReal) ∧
    (prm.c = c → 0 < prm.LV → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 3 * prm.δ ≤ (μ {ω |
        ENNReal.ofReal (regret M P choose play (statesMB P prm choose) prm.K (traj ω)) ≤
          ENNReal.ofReal (12 * Real.sqrt (2 * (H : ℝ) ^ 3 * prm.K * prm.iota) + 0) +
          ∑ h : Fin H, ENNReal.ofReal (6 * (a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT))) *
            ⨅ r₀ : {r : ℝ // 0 < r},
              (ENNReal.ofReal (4 * prm.K * r₀.val) +
                ENNReal.ofReal ((4 * prm.LV * prm.c * Real.sqrt prm.iota) ^ ((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ))) / (1 - 1 / ((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ))))) *
                  ∑' ℓ : ℕ, if r₀.val ≤ (2 : ℝ) ^ (-(ℓ : ℤ)) then
                    ((packingNum D ((2 : ℝ) ^ (-(ℓ : ℤ)))
                        (nearOptSet M (a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT)) h ((2 : ℝ) ^ (-(ℓ : ℤ)))) : ℕ∞) : ENNReal) *
                      ENNReal.ofReal (((2 : ℝ) ^ (-(ℓ : ℤ))) ^ (-(((if prm.dS ≤ 2 then (2 : ℝ) else (prm.dS : ℝ))) - 1)))
                  else 0)}).toReal) := by sorry

end AdaDiscRL
