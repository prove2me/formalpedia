-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_lemma_2_optimal_collection
-- name    : DigitalPrivacy.DataStrategy.lemma_2_optimal_collection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:09:53.308423+00:00
-- url     : https://prove2.me/theorems/8f638f62-1bf7-4122-96b2-7f07e4c3fce2
-- title:
--   Lemma 2 (corrected: not unique at $C=0$ with $P=1$): for fixed protection $C$ the optimal collection is $-\kappa(C)+\sqrt{{\kappa(C)^2+C(1-\beta)}}$ below $C_l$ and $1$ above
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $\psi\ge0$ and $P+(1-P)\rho>0$, and write $\xi^\star(C)=-\kappa(C)+\sqrt{\kappa(C)^2+C(1-\beta)}$.
--
--   1. For every $C\ge0$ with $C<C_l$: $0\le\xi^\star(C)<1$, and $\xi^\star(C)$ maximizes $\xi\mapsto\Pi(\xi,C)$ on $[0,1]$; unless $C=0$ and $P=1$, it is the unique maximizer. For every $C>C_l$, the unique maximizer is $\xi=1$.
--   2. $C\mapsto\xi^\star(C)$ is strictly increasing on $C\ge0$.
--
--   This is the business's best response in collection to a given protection level.
--
--   Differences from the source:
--   - correction: Lemma 2 for every protection level C → at C = 0 with P = 1 the Lean states that ξ*(0) = 0 is a maximizer, but not that it is the only one; reason: at C = 0, P = 1 the profit Π(ξ, 0) is 0 for every ξ ∈ [0, 1], so the maximizer is not unique (e.g. β = 0, ρ = 1/2: Π(1/2, 0) = Π(1, 0) = 0)
--   - encoding: κ(C), C_l and C_inv, which divide by P + (1 − P)ρ → hypothesis 0 < P + (1 − P)ρ; reason: it only excludes P = ρ = 0, where those formulas are undefined
--   - reading: the business stores ξ*(C) (respectively all the information) → the maximizers of ξ ↦ Π(ξ, C) on [0, 1] are exactly ξ*(C) (respectively 1); reason: the lemma names the business's choice; the iff says it is the unique maximizer
--   - generalization: ξ*(C) is increasing in C, stated within the case C < C_l → StrictMonoOn on all C ≥ 0; reason: the closed form is strictly increasing on all of C ≥ 0 (OA B.2's derivative sign does not use C < C_l); restricting to [0, C_l) gives the printed claim
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30); proof OA B.2, Online Appendix p. 2 (PDF 39)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_profit
import Definitions.Def_DigitalPrivacy_DataStrategy_xiOfC
import Definitions.Def_DigitalPrivacy_DataStrategy_cL

namespace DigitalPrivacy.DataStrategy

/-- **Lemma 2 (corrected: at `C = 0` with `P = 1` the maximizer is not unique): optimal data
collection for fixed data protection.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Lemma 2, p. 29 (PDF 30); proof OA B.2, Online Appendix p. 2 (PDF 39): "Given a data
protection level C, the business stores: part of the information ξ⋆(C) = −κ(C) + √(κ(C)² +
C(1 − β)) < 1 (increasing in C) if data protection policy level is low C < Cl; all the information
(ξ⋆(C) = 1) if data protection policy level is high C > Cl."

For `β, ρ ∈ [0, 1)`, `P ∈ [0, 1]`, `ψ ≥ 0` and `P + (1 − P)ρ > 0`, for every `C ≥ 0`:

1. if `C < C_l`: `0 ≤ ξ⋆(C) < 1`, `ξ⋆(C)` maximizes `ξ ↦ Π(ξ, C)` on `[0, 1]`, and, unless
   `C = 0` and `P = 1`, it is the only maximizer;
2. if `C > C_l`: the maximizers of `ξ ↦ Π(ξ, C)` on `[0, 1]` are exactly `1`;
3. `C ↦ ξ⋆(C)` is strictly increasing on `C ≥ 0`.

**Formalization Note.** At `C = 0`, `P = 1` the profit `Π(ξ, 0)` is `0` for every `ξ`, so
`ξ⋆(0) = 0` is a maximizer but not the only one; only uniqueness is dropped there.
`P + (1 − P)ρ > 0` only excludes `P = ρ = 0`, where `κ` and `C_l` divide by zero. "Increasing in
C" is stated on all `C ≥ 0`, not only on `C < C_l`. -/
theorem lemma_2_optimal_collection {β ρ P ψ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 ≤ ψ) (ha : 0 < P + (1 - P) * ρ) :
    (∀ C : ℝ, 0 ≤ C →
      (C < cL β ρ P →
        0 ≤ xiOfC β ρ P C ∧ xiOfC β ρ P C < 1 ∧
        (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, profit β ρ P ψ ξ' C ≤ profit β ρ P ψ (xiOfC β ρ P C) C) ∧
        (¬ (C = 0 ∧ P = 1) →
          ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
            ((∀ ξ' ∈ Set.Icc (0 : ℝ) 1, profit β ρ P ψ ξ' C ≤ profit β ρ P ψ ξ C) ↔
              ξ = xiOfC β ρ P C))) ∧
      (cL β ρ P < C →
        ∀ ξ ∈ Set.Icc (0 : ℝ) 1,
          ((∀ ξ' ∈ Set.Icc (0 : ℝ) 1, profit β ρ P ψ ξ' C ≤ profit β ρ P ψ ξ C) ↔ ξ = 1))) ∧
    StrictMonoOn (xiOfC β ρ P) (Set.Ici 0) := by sorry

end DigitalPrivacy.DataStrategy
