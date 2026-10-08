-- Prove2me | Theorems.Thm_FoundationsML_MaxEnt_maxent_l1_generalization_bound_v2
-- name    : FoundationsML.MaxEnt.maxent_l1_generalization_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:16.517327+00:00
-- url     : https://prove2.me/theorems/1f8ffb77-09e2-4250-b953-f97d0773d57c
-- title:
--   Theorem 12.3 — Maxent $L_1$-regularization generalization bound (corrected constant $2r$; bounded $H$)
-- statement:
--   **Statement (Theorem 12.3, p. 303, PDF p. 320; corrected transcription).** Let $X$ be finite, $p_0>0$ a prior, $\Phi:X\to\mathbb R^N$ features with $\|\Phi\|_\infty\le r$, and $H$ a family of real-valued functions mapping into a bounded interval and containing every $\Phi_j$. Fix $\delta\in(0,1)$. Let $\hat w$ be a solution of the optimization (12.12) for
--   $$\lambda = 2R_m(H) + 2r\sqrt{\frac{\log(2/\delta)}{2m}}.$$
--   Then, with probability at least $1-\delta$ over the draw of an i.i.d. sample $S$ of size $m\ge1$ from $D$,
--   $$L_D(\hat w) \le \inf_w\big[L_D(w) + 2\|w\|_1\lambda\big].$$
--
--   **Formalization Note.** The retired version let $H$ be an arbitrary set of functions, so the retired `RademacherComplexity` (real supremum `⨆ g ∈ H`) returned the junk value $0$ for an unbounded $H$ and $\lambda$ was too small (the accepted disproof used $H=$ `univ`). Now $H$ maps into a bounded interval (Definition 3.1's domain for $R_m(H)$) and the corrected `RademacherComplexity` (`_v2`, supremum over exactly $H$) is used; $X$ being finite with measurable singletons, the measurability of $S\mapsto\hat R_S(H)$ assumed by footnote 3 (p. 30) is automatic. **Correction to the printed source:** the deviation term is $2r\sqrt{\log(2/\delta)/(2m)}$, not $r\sqrt{\log(2/\delta)/(2m)}$. The printed $\lambda$ is not sufficient: with $N=1$, $H=\{\Phi_1\}$, $\Phi_1=\pm r$ on $X=\{0,1\}$ and $D$ uniform, $R_m(H)=0$ and the conclusion $L_D(\hat w)\le L_D(0)$ holds exactly when $|\hat{\mathbb E}_S\Phi_1|\le\lambda$, whose probability is below $1-\delta$ for the printed $\lambda$ (for $\delta=0.1$ it is about $0.78$); Hoeffding's inequality for a $[-r,r]$-valued variable gives deviation $2r\sqrt{\log(2/\delta)/(2m)}$, and inequality (12.5), on which the proof rests, holds with $2r$ (McDiarmid with bounded differences $2r/m$, applied to $\{\Phi_j\}\subseteq H$ and to $\{-\Phi_j\}$, each at confidence $1-\delta/2$). $\delta<1$ is the standing convention. As before, "$\hat w$ solves (12.12)" is the minimization hypothesis inside the event, universally quantified over every minimizer, and $\inf_w$ ranges over all of $\mathbb R^N$ (its range is bounded below by $0$ since $L_D\ge0$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 303, Theorem 12.3 (PDF p. 320) — corrected transcription: the deviation term in λ is 2r·sqrt(log(2/δ)/(2m)) for features with ‖Φ‖_∞ ≤ r (the printed r is insufficient)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_LogLoss
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalLogLoss
import Definitions.Def_FoundationsML_MaxEnt_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.MaxEnt

/-- Theorem 12.3 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 303, PDF p. 320), corrected transcription. Features `Φ : X → ℝ^N` with
`‖Φ‖_∞ ≤ r`, `H` a (bounded) family of real-valued functions containing every `Φ_j`, `X`
finite, prior `p0 > 0`. Fix `δ ∈ (0,1)`. Let `ŵ` be a solution of the optimization (12.12)
for `λ = 2R_m(H) + 2r·sqrt(log(2/δ)/(2m))`. Then, with probability at least `1 − δ` over the
draw of an i.i.d. sample `S` of size `m ≥ 1` from `D`,
`L_D(ŵ) ≤ inf_w [L_D(w) + 2‖w‖_1·λ]`.

**Formalization Note.** Replaces `maxent_l1_generalization_bound`, which let `H` be an
arbitrary set of functions, so that the retired `RademacherComplexity` (real supremum
`⨆ g ∈ H`) returned the junk value `0` for an unbounded `H` and the regularization `λ` was
too small (the disproof used `H = univ`). Now `H` maps into a bounded interval (`hHb`,
Definition 3.1's domain for `R_m(H)`) and the corrected `RademacherComplexity` (`_v2`,
supremum over exactly `H`) is used; `X` being finite with measurable singletons, the
measurability of `S ↦ R̂_S(H)` assumed by footnote 3 (p. 30) is automatic. Correction to the
printed source: the deviation term is `2r·sqrt(log(2/δ)/(2m))`, not `r·sqrt(log(2/δ)/(2m))`.
The printed `λ` is not sufficient: with `H = {Φ_1}`, `N = 1`, `Φ_1 = ±r` and `D` uniform,
`R_m(H) = 0` and the conclusion `L_D(ŵ) ≤ L_D(0)` holds exactly when `|Ê_S Φ_1| ≤ λ`, whose
probability is below `1 − δ` for the printed `λ` (Hoeffding for a `[−r,r]`-valued variable
has deviation `2r·sqrt(log(2/δ)/(2m))`); inequality (12.5), on which the proof rests, holds
with `2r` (McDiarmid with bounded differences `2r/m`). `δ < 1` is the standing convention.
The rest is as before: "`ŵ` solves (12.12)" is the minimization hypothesis inside the event,
universally quantified over every minimizer; `inf_w` ranges over all of `ℝ^N` (its range is
bounded below by `0` since `L_D ≥ 0`). -/
theorem maxent_l1_generalization_bound_v2
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (p0 : X → ℝ) (hp0 : ∀ x, 0 < p0 x)
    (Φ : X → Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) (hΦ : ∀ x j, |Φ x j| ≤ r)
    (H : Set (X → ℝ)) (hHΦ : ∀ j : Fin N, (fun x => Φ x j) ∈ H)
    (hHb : ∃ a b : ℝ, ∀ g ∈ H, ∀ x, g x ∈ Set.Icc a b)
    (D : Measure X) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let lam := 2 * RademacherComplexity D H m + 2 * r * Real.sqrt (Real.log (2 / δ) / (2 * m))
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ ŵ : Fin N → ℝ,
        (∀ w : Fin N → ℝ,
            lam * (∑ j, |ŵ j|) + EmpiricalLogLoss p0 Φ S ŵ ≤
              lam * (∑ j, |w j|) + EmpiricalLogLoss p0 Φ S w) →
        LogLoss p0 Φ D ŵ ≤
          ⨅ w : Fin N → ℝ, (LogLoss p0 Φ D w + 2 * (∑ j, |w j|) * lam)}).toReal := by sorry

end FoundationsML.MaxEnt
