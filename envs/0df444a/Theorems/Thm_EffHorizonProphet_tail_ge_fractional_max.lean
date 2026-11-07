-- Prove2me | Theorems.Thm_EffHorizonProphet_tail_ge_fractional_max
-- name    : EffHorizonProphet.tail_ge_fractional_max
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:52.536195+00:00
-- url     : https://prove2.me/theorems/3d52caa9-42fe-4e35-bf73-1d8c80fc8578
-- title:
--   Eq. (37)–(40) — the truncated tail moment bounds the prophet
-- statement:
--   Let $D$ be admissible with distribution function $F$, let $b\ge1$ be real, and take a rule with acceptance event $A$ and acceptance probability $1/b$. Then:
--
--   1. the fractional i.i.d. maximum is bounded by the truncated tail moment,
--   $$M_b(F)=\int_0^\infty\big(1-F(z)^b\big)\,dz\le b\,\mathbb E[Y\mathbf 1\{A\}];$$
--   2. the prophet value has the survival representation
--   $$\mathbb E\Big[\max_{i\in[n]}X_i\Big]=\int_0^\infty\Big(1-\prod_{s=1}^SF\big(z/\tilde\gamma^{\,s-1}\big)^{n_s}\Big)\,dz,$$
--   with $F(z/0):=1$;
--   3. if $b$ equals the effective horizon $B$, then $\mathbb E[\max_{i\in[n]}X_i]\le B\,\mathbb E[Y\mathbf 1\{A\}]$.
--
--   This is the comparison that makes acceptance probability $1/B$ work for every base law, including laws with atoms.
--
--   Differences from the source:
--   - generalization: the rule with $P(Y>\alpha_1)=1/B$, $b=B$ and equal phases → any real $b\ge1$, any phase lengths, and the randomized event $A$; reason: (38)–(39) use only $b\ge1$ and the acceptance probability, Lemma 15 covers all phase lengths, and Remark 16 says the argument is unchanged with $A$
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: the intermediate equalities with $\alpha_1+B\mathbb E[(Y-\alpha_1)_+]$ in (38)–(39) → only the resulting inequalities are stated; reason: they are steps of the proof of (40)
--   - encoding: integrals are written without qualification → integrability on $(0,\infty)$ is stated as clauses; reason: a Bochner integral of a non-integrable function would be $0$; the base law is admissible, so these hold
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (37)–(39), p.29; Eq. (40), p.30; Remark 16, p.31

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_scaled
import Definitions.Def_EffHorizonProphet_prophet
import Definitions.Def_EffHorizonProphet_effHorizon
import Definitions.Def_EffHorizonProphet_acceptProb
import Definitions.Def_EffHorizonProphet_tailValue

open MeasureTheory

namespace EffHorizonProphet

/-- **Eq. (37)–(40)** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), pp.29–30, with atoms by Remark 16, p.31): for real `b ≥ 1` and a rule
with acceptance probability `1/b`, `M_b(F) = ∫₀^∞ (1 - F(z)^b) dz ≤ b E[Y 1{A}]`; the prophet value
is the survival integral `∫₀^∞ (1 - ∏_s F(z/γ̃^{s-1})^{n_s}) dz`; and at `b = B`,
`E[max_i X_i] ≤ B E[Y 1{A}]`.

**Formalization Note** The integrability clauses keep the integrals genuine. `F(z/0) := 1` is
`scaled`. -/
theorem tail_ge_fractional_max {S : ℕ} (hS : 1 ≤ S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (L : Fin S → ℕ) (D : Measure ℝ) (hD : IsAdmissible D) (b : ℝ) (hb : 1 ≤ b) (ρ : Rule)
    (hρ : acceptProb D ρ = 1 / b) :
    IntegrableOn (fun z => 1 - ProbabilityTheory.cdf D z ^ b) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi 0, (1 - ProbabilityTheory.cdf D z ^ b) ≤ b * tailValue D ρ ∧
      IntegrableOn
        (fun z => 1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D) (γ ^ (s : ℕ)) z ^ L s)
        (Set.Ioi 0) ∧
      prophet γ L D =
        ∫ z in Set.Ioi 0, (1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D) (γ ^ (s : ℕ)) z ^ L s) ∧
      (effHorizon γ L = b → prophet γ L D ≤ b * tailValue D ρ) := by sorry

end EffHorizonProphet
