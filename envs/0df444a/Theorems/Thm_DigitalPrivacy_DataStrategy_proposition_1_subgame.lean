-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_proposition_1_subgame
-- name    : DigitalPrivacy.DataStrategy.proposition_1_subgame
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:09:05.096862+00:00
-- url     : https://prove2.me/theorems/67b1717f-8c83-41eb-b884-787e242535a7
-- title:
--   Proposition 1: the users–adversaries subgame has the unique equilibrium (3), consumer surplus $\bar a^{*2}/2$, activity and collected data increasing in $C$ and single-peaked in $\xi$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8).
--
--   1. For every $\xi\in[0,1]$ and $C>0$, the users–adversaries subgame has the unique equilibrium
--   $$\bar a^*(\xi,C)=\frac{C(1+\rho\xi)}{C(1-\beta)+\xi^2},\qquad \omega^*(\xi,C)=\frac{\xi\bar a^*(\xi,C)}{C},$$
--   and the consumer surplus $U_i(\bar a^*,\bar a^*)$ at $\omega^*$ equals $\tfrac12\bar a^*(\xi,C)^2$.
--   2. For every $\xi\in[0,1]$, $C\mapsto\bar a^*(\xi,C)$ and $C\mapsto\xi\bar a^*(\xi,C)$ are nondecreasing on $C>0$, and strictly increasing when $\xi>0$.
--   3. For every $C>0$ there are $0\le\underline\xi\le\bar\xi\le1$ such that $\xi\mapsto\bar a^*(\xi,C)$ strictly increases on $[0,\underline\xi]$ and strictly decreases on $[\underline\xi,1]$, and $\xi\mapsto\xi\bar a^*(\xi,C)$ strictly increases on $[0,\bar\xi]$ and strictly decreases on $[\bar\xi,1]$.
--
--   Item 1 justifies evaluating the business's profit at $\bar a^*$; items 2–3 describe how data protection and data collection move users' activity.
--
--   Differences from the source:
--   - encoding: a Bayesian equilibrium (a*, v*) of users' and adversaries' strategy profiles in the subgame after (ξ, C), with M → ∞ → SubgameEquilibrium: a symmetric pair (ā, ω), ā a best reply over a ≥ 0 to correct expectations and ω = āξ/C, for C > 0; reason: users are homogeneous with a unique best reply, so equilibria are symmetric; the adversaries' mass āξ/C is the M → ∞ limit (A.1); ω* = ξā*/C is undefined at C = 0
--   - reading: CS(ξ, C) = ∫ Uᵢ(aᵢ*, ā*) di → userUtility at a = ā = ā*, ω = ω*; reason: users are a unit mass of identical agents playing ā* (A.1, p. 28)
--   - reading: (a) ā* and ξā* increase in data protection C → MonotoneOn on C > 0, and StrictMonoOn when ξ > 0; reason: at ξ = 0 both functions are constant in C, so strict increase holds exactly for ξ > 0
--   - reading: footnote 15: increases on [0, ξ(C)] and decreases otherwise → StrictMonoOn on [0, ξ_lo], StrictAntiOn on [ξ_lo, 1] (same for ξ_hi), with 0 ≤ ξ_lo ≤ ξ_hi ≤ 1; reason: A.1 defines ξ(C) = min{1, ξ₁(C)} and ξ̄(C) = min{1, ξ₂(C)}, and ξ ranges over [0, 1]
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Proposition 1, p. 10 (PDF 11), with footnote 15; proof App. A.1, p. 28 (PDF 29)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_SubgameEquilibrium
import Definitions.Def_DigitalPrivacy_DataStrategy_abarStar

namespace DigitalPrivacy.DataStrategy

/-- **Proposition 1: the users–adversaries subgame.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Proposition 1, p. 10 (PDF 11), with footnote 15; proof App. A.1, p. 28 (PDF 29):
"Fix the business's data strategy (ξ, C). The ensuing subgame has a unique equilibrium in which
users' and adversaries' activities are: ā∗(ξ, C) = C(1 + ρξ)/(C(1 − β) + ξ²) and ω∗(ξ, C) =
ξā∗(ξ, C)/C, (3) and the resulting consumer surplus is: CS(ξ, C) = ½ā∗(ξ, C)². (4) Furthermore,
equilibrium users' activity, ā∗(ξ, C) and users' data collected, ξā∗(ξ, C) both: (a) Increase in
data protection C; (b) First increase and then decrease in data collection ξ." Footnote 15: "there
exist 0 ≤ ξ(C) ≤ ξ̄(C) such that (i) ā∗(ξ, C) increases with ξ for ξ ∈ [0, ξ(C)] and decreases
otherwise; (ii) ξā∗(ξ, C) increases with ξ for ξ ∈ [0, ξ̄(C)] and decreases otherwise."

Standing assumptions: `β ∈ [0, 1)`, `ρ ∈ [0, 1)` (p. 6), `ξ ∈ [0, 1]` (p. 8).

1. For `ξ ∈ [0, 1]` and `C > 0`: `(ā, ω)` is a subgame equilibrium iff it is (3); `abarStar`
   is (3); and the consumer surplus `Uᵢ(ā*, ā*)` at `ω*` equals `½ā*²`, (4).
2. (a) For `ξ ∈ [0, 1]`, `C ↦ ā*(ξ, C)` and `C ↦ ξā*(ξ, C)` are monotone on `C > 0`, strictly
   when `ξ > 0`.
3. (b) For `C > 0` there are `0 ≤ ξ_lo ≤ ξ_hi ≤ 1` with `ā*(·, C)` strictly increasing on
   `[0, ξ_lo]` and strictly decreasing on `[ξ_lo, 1]`, and `ξā*(·, C)` strictly increasing on
   `[0, ξ_hi]` and strictly decreasing on `[ξ_hi, 1]`.

**Formalization Note.** The subgame equilibrium is in symmetric reduced form (`SubgameEquilibrium`):
users are homogeneous with a unique best reply. It is stated for `C > 0`, where `ω* = ξā*/C` is
defined. CS is `∫ Uᵢ` over the unit mass of identical users (A.1). "Increase in C" holds strictly
for `ξ > 0`; at `ξ = 0` both functions are constant in `C`. The footnote's thresholds are capped at
`1` as in A.1 (`ξ(C) = min{1, ξ₁(C)}`, `ξ̄(C) = min{1, ξ₂(C)}`); "decreases otherwise" is read on
`[ξ(C), 1]`. -/
theorem proposition_1_subgame {β ρ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∀ ξ C : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 → 0 < C →
      (∀ abar ω : ℝ, SubgameEquilibrium β ρ ξ C abar ω ↔
          abar = C * (1 + ρ * ξ) / (C * (1 - β) + ξ ^ 2) ∧ ω = ξ * abar / C) ∧
      abarStar β ρ ξ C = C * (1 + ρ * ξ) / (C * (1 - β) + ξ ^ 2) ∧
      userUtility β ρ ξ (ξ * abarStar β ρ ξ C / C) (abarStar β ρ ξ C) (abarStar β ρ ξ C) =
        (1 / 2) * abarStar β ρ ξ C ^ 2) ∧
    (∀ ξ : ℝ, ξ ∈ Set.Icc (0 : ℝ) 1 →
      MonotoneOn (fun C => abarStar β ρ ξ C) (Set.Ioi 0) ∧
      MonotoneOn (fun C => ξ * abarStar β ρ ξ C) (Set.Ioi 0) ∧
      (0 < ξ → StrictMonoOn (fun C => abarStar β ρ ξ C) (Set.Ioi 0) ∧
        StrictMonoOn (fun C => ξ * abarStar β ρ ξ C) (Set.Ioi 0))) ∧
    (∀ C : ℝ, 0 < C → ∃ ξlo ξhi : ℝ, 0 ≤ ξlo ∧ ξlo ≤ ξhi ∧ ξhi ≤ 1 ∧
      StrictMonoOn (fun ξ => abarStar β ρ ξ C) (Set.Icc 0 ξlo) ∧
      StrictAntiOn (fun ξ => abarStar β ρ ξ C) (Set.Icc ξlo 1) ∧
      StrictMonoOn (fun ξ => ξ * abarStar β ρ ξ C) (Set.Icc 0 ξhi) ∧
      StrictAntiOn (fun ξ => ξ * abarStar β ρ ξ C) (Set.Icc ξhi 1)) := by sorry

end DigitalPrivacy.DataStrategy
