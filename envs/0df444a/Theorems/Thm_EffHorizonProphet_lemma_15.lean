-- Prove2me | Theorems.Thm_EffHorizonProphet_lemma_15
-- name    : EffHorizonProphet.lemma_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:56.908165+00:00
-- url     : https://prove2.me/theorems/c43b3233-49fe-4956-b956-868bf72eb518
-- title:
--   Lemma 15 — effective-horizon comparison for general phases
-- statement:
--   Let $F$ be the distribution function of an admissible base law. Fix $S\ge1$, phase lengths $n_1,\dots,n_S\in\mathbb N$, and decay factors $(\gamma_t)_{t=1}^{S-1}\in[0,1]^{S-1}$, and set $\Gamma_s=\prod_{t=1}^s\gamma_t$, $\Gamma_0=1$ and $B_G=\sum_{s=1}^S\Gamma_{s-1}n_s$. Then
--   $$\int_0^\infty\big(1-F(z)^{B_G}\big)\,dz\ge\int_0^\infty\Big(1-\prod_{s=1}^SF\big(z/\Gamma_{s-1}\big)^{n_s}\Big)\,dz,$$
--   with the convention $F(z/0):=\lim_{u\to\infty}F(u)=1$ for $z\ge0$. Both integrals are finite.
--
--   The decayed sequence is therefore dominated, in expected maximum, by an i.i.d. maximum over the effective horizon $B_G$, a real number used through the fractional power $F^{B_G}$.
--
--   Differences from the source:
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: "all integrals are finite" is asserted in the proof (p.27) → both integrability statements on $(0,\infty)$ are clauses of the theorem; reason: a Bochner integral of a non-integrable function would be $0$; the base law is admissible, so these hold
--   - reading: "the base reward distribution $D$" (a law on $\mathbb R_+$, p.3) → $D$ admissible, i.e. in the class $\mathcal D$ of p.4 ($0<\mathbb E_D[Y]<\infty$); reason: the proof (p.27) takes all integrals finite "by the assumption $\int_0^\infty(1-F(z)^N)\,dz<\infty$", which is the finite mean of $\mathcal D$; the excluded $\mathbb E_D[Y]=0$ case has both sides $0$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 15, Eq. (33), p.27

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_scaled

open MeasureTheory

namespace EffHorizonProphet

/-- **Lemma 15** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.27): for a base law with cdf `F`, phase lengths `n_1, …, n_S` and decay
factors `(γ_t)_{t=1}^{S-1}` in `[0, 1]`, with `Γ_s = ∏_{t ≤ s} γ_t`, `Γ_0 = 1` and
`B_G = ∑_s n_s Γ_{s-1}`,
`∫₀^∞ (1 - F(z)^{B_G}) dz ≥ ∫₀^∞ (1 - ∏_s F(z/Γ_{s-1})^{n_s}) dz`, with `F(z/0) := 1`.

**Formalization Note** Indices are `0`-based: `g t` is the paper's `γ_{t+1}`, and `g` is read only at
`t + 1 < S`. Both integrability clauses are stated, so neither side is a Bochner junk value. The right
exponent is a real power. -/
theorem lemma_15 (D : Measure ℝ) (hD : IsAdmissible D) (S : ℕ) (hS : 1 ≤ S) (n : Fin S → ℕ)
    (g : ℕ → ℝ) (hg0 : ∀ t, t + 1 < S → 0 ≤ g t) (hg1 : ∀ t, t + 1 < S → g t ≤ 1) :
    IntegrableOn
        (fun z => 1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D)
          (∏ t ∈ Finset.range (s : ℕ), g t) z ^ n s) (Set.Ioi 0) ∧
      IntegrableOn
        (fun z => 1 - ProbabilityTheory.cdf D z ^
          (∑ s : Fin S, (n s : ℝ) * ∏ t ∈ Finset.range (s : ℕ), g t)) (Set.Ioi 0) ∧
      ∫ z in Set.Ioi 0, (1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D)
          (∏ t ∈ Finset.range (s : ℕ), g t) z ^ n s) ≤
        ∫ z in Set.Ioi 0, (1 - ProbabilityTheory.cdf D z ^
          (∑ s : Fin S, (n s : ℝ) * ∏ t ∈ Finset.range (s : ℕ), g t)) := by sorry

end EffHorizonProphet
