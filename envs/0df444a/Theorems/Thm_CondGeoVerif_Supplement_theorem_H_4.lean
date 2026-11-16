-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_H_4
-- name    : CondGeoVerif.Supplement.theorem_H_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:20:21.03143+00:00
-- url     : https://prove2.me/theorems/333f8793-f363-4c94-9071-6bb83001ea70
-- title:
--   Theorem H.4 — localized lower bound $m>\varepsilon^{-1}(\sqrt{d-1}/(20C_a)-L_a)$, hence $\Omega_a(\sqrt d/\varepsilon)$, for $0<a<a_c$
-- statement:
--   Let $d\ge2$, $X=(T,Z)\sim N(0,I_d)$, $h_0(X)=\mathrm{sign}(T)$, $\mathrm{OPT}_P$ the infimum of risk under $P$ over homogeneous halfspaces, and $0<a<a_c$. Take an admissible cutoff $M$ and the constants $J_a,H_a,\theta_a,\varepsilon_a$, $C_a=16M/J_a$ of §H.2, and $0<\varepsilon\le\varepsilon_a$. Let $Q$ be the null with regression $r_0=ah_0$ and $P_v$, $v\in S^{d-2}$, the localized alternatives of §H.2 with regressions $r_v$.
--
--   Suppose a protocol is complete with probability at least $2/3$ at $Q$, and for every displayed $P_v$ and every prover strategy is sound with probability at least $2/3$ at excess risk $\varepsilon$. Then, with
--   $$L_a=1+\log(24)\Big(8C_a+\frac83\Big),$$
--   its verifier sample complexity satisfies
--   $$m>\frac1\varepsilon\Big(\frac{\sqrt{d-1}}{20C_a}-L_a\Big).$$
--   In particular, for $d-1\ge(40C_aL_a)^2$, $m\ge\sqrt{d-1}/(40C_a\varepsilon)=\Omega_a(\sqrt d/\varepsilon)$. For any prescribed local radius $\tau>0$, these soundness alternatives all satisfy $\|r_v-r_0\|_2\le\tau$ whenever additionally $\varepsilon\le\tau^2/((1-a^2)C_a)$.
--
--   The protocol may interact arbitrarily and output improper measurable predictors.
--
--   Differences from the source:
--   - reading: M = M_a ≥ max{1, k_a} chosen so large that (1 + a)∫_M^∞ q ≤ J_a/4 → the theorem for every such M, with all constants computed from it; reason: covers every choice the paper may make
--   - reading: any verifier with arbitrary interaction and every prover strategy → the published IVerifier (finitely many rounds, measurable queries and outputs) and soundness against every measurable prover strategy; reason: same model as the live goal Theorem 3.1 and Theorem B.1; the paper's simulated honest prover is a measurable randomized strategy
--   - encoding: Q and the displayed P_v → laws given by IsLabelLaw with base rule h₀ and error probabilities η_a and z_v; reason: the regressions r₀ = ah₀ and r_v = h₀(1 − 2z_v) are the same laws
--   - encoding: v ∈ S^{d−2} → a unit w ∈ ℝ^d with w₁ = 0; reason: v·Z = w·x
--   - encoding: labels in {−1, 1}; a sign on a zero hyperplane can be chosen arbitrarily → labels Bool (true ↔ +1), sign(0) = +1; reason: hyperplanes are Gaussian-null, so no probability in the statement depends on the convention (App. C, p.28)
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem H.4, p.67 (PDF p.70); construction §H.1–H.2, pp.64–65 (PDF pp.67–68)

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_zAlt

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem H.4** (Chen, *The Conditional Geometry of Statistical Verification*, manuscript,
October 2026, sha256 07a66d18…, p.67 = PDF p.70, with the construction of §H.2, p.65). Let `d ≥ 2`,
`X = (T, Z) ∼ N(0, I_d)`, `h₀ = sign(T)`, `0 < a < a_c`, an admissible cutoff `M` and the constants
`J_a, H_a, θ_a, ε_a, C_a = 16M/J_a` of §H.2, and `0 < ε ≤ ε_a`. Let `Q` be the null with regression
`ah₀`, and `P_v` (`v ∈ S^{d−2}`) the alternatives of §H.2. Suppose an interactive, possibly improper
protocol is complete with probability at least `2/3` at `Q`, and for every displayed `P_v` and every
prover strategy is sound with probability at least `2/3` at excess risk `ε` (against homogeneous
halfspaces). Then, with `L_a = 1 + log(24)(8C_a + 8/3)`, its verifier sample complexity satisfies
`m > (1/ε)(√(d − 1)/(20C_a) − L_a)`; in particular, for `d − 1 ≥ (40C_aL_a)²`,
`m ≥ √(d − 1)/(40C_aε)`. For any prescribed local radius `τ > 0`, these alternatives all satisfy
`‖r_v − r₀‖₂ ≤ τ` whenever additionally `ε ≤ τ²/((1 − a²)C_a)`.

**Formalization Note** "Choose `M` so large that …" is a choice: the theorem holds for every
admissible `M` (`IsAdmissibleM`) with all constants computed from it. `v ∈ S^{d−2}` is a unit
`w ∈ ℝᵈ` with first coordinate `0`. `Q` and `P_v` are given by `IsLabelLaw` with base rule `h₀` and
error probabilities `η_a` and `zAlt` (regressions `r₀ = ah₀`, `r_v = h₀(1 − 2z_v)`). Soundness is
required only at the laws `P_v` (`ISoundOn`), against measurable strategies, as in the published
`ISound`. `‖·‖₂` is the `L²(N(0, I_d))` norm. -/
theorem theorem_H_4 {a : ℝ} (ha0 : 0 < a) (ha : a < aC) (M : ℝ) (hM : IsAdmissibleM a M) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ epsA a M) {d : ℕ} (hd : 2 ≤ d) :
    (∀ (V : IVerifier d) (Q : ProbabilityMeasure (Vec d × Bool)),
      IsLabelLaw (Q : Measure (Vec d × Bool)) (h0 d) (fun _ => etaA a) →
      ICompleteAt V Q (halfspaceClass d) ε (1 / 3) →
      ISoundOn V {P | ∃ w : Vec d, firstCoord w = 0 ∧ ‖w‖ = 1 ∧
          IsLabelLaw (P : Measure (Vec d × Bool)) (h0 d) (zAlt a M ε w)}
        (halfspaceClass d) ε (1 / 3) →
      1 / ε * (Real.sqrt ((d : ℝ) - 1) / (20 * CA a M) - LA a M) < (V.m : ℝ) ∧
      ((40 * CA a M * LA a M) ^ 2 ≤ (d : ℝ) - 1 →
        Real.sqrt ((d : ℝ) - 1) / (40 * CA a M * ε) ≤ (V.m : ℝ))) ∧
    (∀ τ : ℝ, 0 < τ → ε ≤ τ ^ 2 / ((1 - a ^ 2) * CA a M) →
      ∀ w : Vec d, firstCoord w = 0 → ‖w‖ = 1 →
        Real.sqrt (∫ x, (rAlt a M ε w x - a * sgnR (firstCoord x)) ^ 2 ∂(gauss d)) ≤ τ) := by sorry

end CondGeoVerif.Supplement
