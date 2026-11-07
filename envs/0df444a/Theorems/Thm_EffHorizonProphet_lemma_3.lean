-- Prove2me | Theorems.Thm_EffHorizonProphet_lemma_3
-- name    : EffHorizonProphet.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:05.757755+00:00
-- url     : https://prove2.me/theorems/9d4aaf09-ff10-4a6c-a1e4-6088bfd2e374
-- title:
--   Lemma 3 — effective-horizon comparison for equal phases
-- statement:
--   Let $F$ be the distribution function of an admissible base law. With a common decay factor $\tilde\gamma\in[0,1]$, $S\ge1$ phases of equal length $m=n/S$ and $B=m\sum_{s=0}^{S-1}\tilde\gamma^s$,
--   $$\int_0^\infty\big(1-F(z)^B\big)\,dz\ge\int_0^\infty\Big(1-\prod_{s=1}^SF\big(z/\tilde\gamma^{\,s-1}\big)^{n/S}\Big)\,dz,$$
--   with the convention $F(z/0):=1$ for $z\ge0$.
--
--   This identifies $B$ as an effective i.i.d. horizon for the decayed prophet benchmark and motivates the acceptance probability $1/B$.
--
--   Differences from the source:
--   - encoding: phases and stages are numbered from $1$ → they are numbered from $0$; reason: a relabelling: paper phase $s$ is Lean phase $s-1$
--   - encoding: phase length $n/S$ → an integer $m$; reason: the printed setting has $S\mid n$
--   - encoding: integrals are written without qualification → both integrability statements are clauses of the theorem; reason: a Bochner integral of a non-integrable function would be $0$; the base law is admissible, so these hold
--   - reading: "the base reward distribution $D$" (a law on $\mathbb R_+$, p.3) → $D$ admissible, i.e. in the class $\mathcal D$ of p.4 ($0<\mathbb E_D[Y]<\infty$); reason: the proof (p.27) takes all integrals finite "by the assumption $\int_0^\infty(1-F(z)^N)\,dz<\infty$", which is the finite mean of $\mathcal D$; the excluded $\mathbb E_D[Y]=0$ case has both sides $0$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 3, Eq. (5), p.8

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_scaled

open MeasureTheory

namespace EffHorizonProphet

/-- **Lemma 3** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.8): for a common decay factor and equal-length phases `n/S = m`, with
`B = m ∑_{s<S} γ̃^s`,
`∫₀^∞ (1 - F(z)^B) dz ≥ ∫₀^∞ (1 - ∏_s F(z/γ̃^{s-1})^{n/S}) dz`, with `F(z/0) := 1`.

**Formalization Note** Both integrability clauses are stated, so neither side is a junk value. -/
theorem lemma_3 (D : Measure ℝ) (hD : IsAdmissible D) (S : ℕ) (hS : 1 ≤ S) (m : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    IntegrableOn
        (fun z => 1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D) (γ ^ (s : ℕ)) z ^ m)
        (Set.Ioi 0) ∧
      IntegrableOn
        (fun z => 1 - ProbabilityTheory.cdf D z ^ ((m : ℝ) * ∑ s ∈ Finset.range S, γ ^ s))
        (Set.Ioi 0) ∧
      ∫ z in Set.Ioi 0, (1 - ∏ s : Fin S, scaled (ProbabilityTheory.cdf D) (γ ^ (s : ℕ)) z ^ m) ≤
        ∫ z in Set.Ioi 0,
          (1 - ProbabilityTheory.cdf D z ^ ((m : ℝ) * ∑ s ∈ Finset.range S, γ ^ s)) := by sorry

end EffHorizonProphet
