-- Prove2me | Theorems.Thm_AdaDiscRL_theorem_4_1
-- name    : AdaDiscRL.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:31:08.430138+00:00
-- url     : https://prove2.me/theorems/a63bb343-f6dc-4f51-a1f5-deb93f0624e3
-- title:
--   Theorem 4.1 — AdaMB and AdaQL regret scales with the zooming dimension (corrected: denominator $z_h+d_{\mathcal S}$; AdaMB factor $(1+L_V)^{\gamma/(z_h+\gamma)}$; $c_h$ explicit)
-- statement:
--   There are absolute constants $c,a,C>0$ and $p\in\mathbb N$ such that the following holds. Let $\mathcal S,\mathcal A$ be compact metric spaces, $\mathcal D$ a metric on $\mathcal S\times\mathcal A$ with $\mathcal D\le\mathcal D_{\mathcal S}+\mathcal D_{\mathcal A}$, $\mathcal P$ a hierarchical partition with levels $0,\dots,K$ whose state cells have $2^{d_{\mathcal S}}$ children, $M$ an episodic MDP with horizon $H\ge1$, $K\ge1$ and $\delta\in(0,1)$. Put
--   $$
--   L=1+L_r+L_V+L_VL_T,\qquad \iota=\log(2HK^2/\delta),
--   $$
--   and let $z_h$ be the step-$h$ zooming dimension with constant $c_h$ for $C_L=aL$. Then for every run (any starting states) the following hold with probability at least $1-3\delta$:
--
--   1. AdaMB with bonus constant $c$, $d_{\mathcal S}>2$, Assumptions 1 and 2:
--   $$
--   \mathrm{Regret}(K)\le C\iota^p\Big(H^{3/2}\sqrt K+L\sum_{h=1}^H\big((1+L_V)^{d_{\mathcal S}}c_h\big)^{\frac1{z_h+d_{\mathcal S}}}K^{\frac{z_h+d_{\mathcal S}-1}{z_h+d_{\mathcal S}}}\Big);
--   $$
--   2. AdaMB with bonus constant $c$, $d_{\mathcal S}\le2$, Assumptions 1 and 2:
--   $$
--   \mathrm{Regret}(K)\le C\iota^p\Big(H^{3/2}\sqrt K+L\sum_{h=1}^H\big((1+L_V)^{2}c_h\big)^{\frac1{z_h+2}}K^{\frac{z_h+1}{z_h+2}}\Big);
--   $$
--   3. AdaQL under Assumption 1:
--   $$
--   \mathrm{Regret}(K)\le C\iota^p\,L H^{3/2}\sum_{h=1}^H c_h^{\frac1{z_h+2}}K^{\frac{z_h+1}{z_h+2}} .
--   $$
--   The regret thus grows with the zooming dimension of the near-optimal set rather than with the ambient dimension $d_{\mathcal S}+d_{\mathcal A}$.
--
--   **Formalization Note** The paper's $\lesssim$ (poly-logarithmic factors of $1/\delta,H,K$ and universal constants) is $C\iota^p$ with $C,p$ universal, quantified before every type.
--
--   Differences from the source:
--   - correction: AdaMB, d_S > 2: exponent (z_h + d_S − 1)/(d + d_S) → (z_h + d_S − 1)/(z_h + d_S); reason: H = 1, S = [0,1]³, A = [0,1]², r = 1 − ‖a‖∞: every played center has gap ≥ C̃K^{−1/3}/4, so Regret ≥ (C̃/4)K^{2/3}, above polylog·(√K + K^{5/8}) (correction C1; matches Informal Theorem 1, Table 1 and F.3)
--   - correction: AdaMB: factor L → L (1 + L_V)^{γ/(z_h+γ)} (γ = d_S or 2), written as ((1 + L_V)^γ c_h)^{1/(z_h+γ)}; reason: F.3 multiplies C_L by C̃^{1/α} with C̃ ∝ L_V; the family r = 1/2 + (ε − Ma)₊ (d_S = 1) has Regret ≍ c²M³ι 2^{3ℓ₀} against the printed (1+2M)K₀^{3/4} ≍ M^{5/2}…, ratio ≥ M^{1/2}/polylog (correction C2)
--   - correction: no c_h in the bound → the factor c_h^{1/(z_h+γ)}; reason: c_h is instance dependent; the C2 family with ε ≍ K^{−1/4} and c₁ ≍ 1/ε has z₁ ≤ 1 but regret ≍ K^{3/4} > polylog·K^{2/3} (correction C3)
--   - correction: zooming dimension: N_r(Z_h^r) ≤ c_h r^{−d} for all r > 0 → for r ∈ (0, 1]; reason: for r > 1 the printed set is empty for every c_h (correction C4)
--   - reading: hierarchical partition of Definition 3.1 (diam ≤ 2^{−ℓ}) → diam = 2^{−ℓ}, centers in regions, state cells partition S with 2^{d_S} children, regions measurable; reason: stated on pp.15, 17, 19, 36, 39, 53 (reading R1)
--   - reading: C_L an absolute constant depending on the Lipschitz constants → C_L = a L with a universal a > 0; reason: reading R2
--   - reading: ≲ omits poly-logarithmic factors of 1/δ, H, K, d and universal constants → C ι^p with universal C > 0, p ∈ ℕ quantified before the types; reason: reading R3
--   - reading: c an absolute constant in Tucb (p.17) → ∃ c > 0 quantified before all types, and the run uses prm.c = c; reason: the paper fixes c once (reading R4)
--   - generalization: d_S the covering dimension of S → d_S given by the partition (2^{d_S} sub-cells per state cell); no covering-dimension hypothesis; reason: under R1 the partition forces N_r(S) ≤ 2^{d_S} r^{−d_S}, which is all the analysis uses; the source's instances satisfy it
--   - generalization: polylog factors may depend on d → C and p do not depend on d; reason: a statement with d-free constants implies the printed one
--   - generalization: initial estimates H − h + 1 (Algorithm 1, line 2) or H (Lemma 3.2, proof of D.1) → any v₀(h) ∈ [H − h + 1, H]; reason: covers both printed initializations (reading R7)
--   - generalization: AdaMB/AdaQL run with a given sequence of starting states {X_1^k}, action ã(B_h^k) (or a distribution on the ball), argmax with ties, rewards and transitions drawn from R_h and T_h → IsRun: starting states arbitrary random variables, action law any kernel supported on the ball's action cell, any argmax rule, only the conditional marginals of R_h^k and X_{h+1}^k fixed; reason: each choice of the source is a special case (reading R8); the statement holds for every such run
--   - encoding: levels ℓ = 0, …, K of Definition 3.1 → HierPartition with Lmax = K; a ball of level K has no children and is never split; reason: Definition 3.1's level range
--   - encoding: steps h ∈ [H] = {1, …, H}, V̄_{H+1} = V⋆_{H+1} = 0 → h : Fin H (0-based: Lean h is step h + 1), with the value at step H + 1 set to 0; reason: Lean indexing; same instances
-- source:
--   Sinclair, Banerjee & Yu, Adaptive Discretization in Online Reinforcement Learning, arXiv:2110.15843v3, Theorem 4.1, p.20

import Mathlib
import Definitions.Def_AdaDiscRL_adaMB
import Definitions.Def_AdaDiscRL_IsRun
import Definitions.Def_AdaDiscRL_Assumption1
import Definitions.Def_AdaDiscRL_Assumption2
import Definitions.Def_AdaDiscRL_regret
import Definitions.Def_AdaDiscRL_IsZoomingDim
import Definitions.Def_AdaDiscRL_IsAdmissibleMetric

open MeasureTheory ProbabilityTheory Classical

namespace AdaDiscRL

/-- **Theorem 4.1** (arXiv:2110.15843v3, p.20), corrected. There are absolute constants `c, a, C > 0`
and `p ∈ ℕ` such that the following holds. Let `S`, `A` be compact metric spaces, `D` a metric on
`S × A` with `D ≤ D_S + D_A`, `P` a hierarchical partition of `S × A` (levels `0, …, K`, state cells
with `2^{d_S}` children), `M` an episodic MDP with horizon `H ≥ 1`, `K ≥ 1`, `δ ∈ (0, 1)`,
`L = 1 + L_r + L_V + L_V L_T`, `ι = log(2HK²/δ)`, and let `z_h` be the step-`h` zooming dimension
with constant `c_h` for `C_L = a L`. Then for any sequence of starting states, with probability at
least `1 − 3δ`:
1. AdaMB (constant `c`), `d_S > 2`, Assumptions 1 and 2:
   `Regret(K) ≤ C ι^p (H^{3/2}√K + L Σ_h ((1+L_V)^{d_S} c_h)^{1/(z_h+d_S)} K^{(z_h+d_S−1)/(z_h+d_S)})`;
2. AdaMB (constant `c`), `d_S ≤ 2`, Assumptions 1 and 2:
   `Regret(K) ≤ C ι^p (H^{3/2}√K + L Σ_h ((1+L_V)² c_h)^{1/(z_h+2)} K^{(z_h+1)/(z_h+2)})`;
3. AdaQL, Assumption 1: `Regret(K) ≤ C ι^p L H^{3/2} Σ_h c_h^{1/(z_h+2)} K^{(z_h+1)/(z_h+2)}`.

**Formalization Note.** `≲` (polylog factors of `1/δ, H, K` and universal constants) is `C ι^p`
with `C, p` universal and quantified before every type. Corrections: the printed denominator `d + d_S`
is `z_h + d_S`; the AdaMB Lipschitz factor carries `(1 + L_V)^{γ/(z_h+γ)}`; `c_h^{1/(z_h+γ)}` appears
(γ = `d_S` or `2`). -/
theorem theorem_4_1 : ∃ (c a C : ℝ) (p : ℕ), 0 < c ∧ 0 < a ∧ 0 < C ∧
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
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (traj : Ω → ℕ → EpData S A H)
    (cz z : Fin H → ℝ),
    (∀ h, IsZoomingDim M D (a * (1 + prm.Lr + prm.LV + prm.LV * prm.LT)) h (cz h) (z h)) →
    (2 < prm.dS → prm.c = c → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 3 * prm.δ ≤ (μ {ω | regret M P choose play (statesMB P prm choose) prm.K (traj ω) ≤
        C * prm.iota ^ p * ((H : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt prm.K +
          (1 + prm.Lr + prm.LV + prm.LV * prm.LT) * ∑ h : Fin H, ((1 + prm.LV) ^ prm.dS * cz h) ^ (1 / (z h + prm.dS)) * (prm.K : ℝ) ^ ((z h + prm.dS - 1) / (z h + prm.dS)))}).toReal) ∧
    (prm.dS ≤ 2 → prm.c = c → Assumption1 M D prm.LV → Assumption2 M D prm.Lr prm.LT →
      IsRun M P choose play (statesMB P prm choose) prm.K μ traj →
      1 - 3 * prm.δ ≤ (μ {ω | regret M P choose play (statesMB P prm choose) prm.K (traj ω) ≤
        C * prm.iota ^ p * ((H : ℝ) ^ (3 / 2 : ℝ) * Real.sqrt prm.K +
          (1 + prm.Lr + prm.LV + prm.LV * prm.LT) * ∑ h : Fin H, ((1 + prm.LV) ^ 2 * cz h) ^ (1 / (z h + 2)) * (prm.K : ℝ) ^ ((z h + 1) / (z h + 2)))}).toReal) ∧
    (Assumption1 M D prm.LV →
      IsRun M P choose play (statesQL P prm choose) prm.K μ traj →
      1 - 3 * prm.δ ≤ (μ {ω | regret M P choose play (statesQL P prm choose) prm.K (traj ω) ≤
        C * prm.iota ^ p * ((1 + prm.Lr + prm.LV + prm.LV * prm.LT) * (H : ℝ) ^ (3 / 2 : ℝ) *
          ∑ h : Fin H, (cz h) ^ (1 / (z h + 2)) * (prm.K : ℝ) ^ ((z h + 1) / (z h + 2)))}).toReal) := by sorry

end AdaDiscRL
