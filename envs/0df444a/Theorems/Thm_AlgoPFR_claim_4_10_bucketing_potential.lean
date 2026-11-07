-- Prove2me | Theorems.Thm_AlgoPFR_claim_4_10_bucketing_potential
-- name    : AlgoPFR.claim_4_10_bucketing_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:42.827047+00:00
-- url     : https://prove2.me/theorems/a6d3aea8-de1f-438d-a6c4-988c8f86be00
-- title:
--   Claim 4.10 — bucketing raises the potential by at most $2\log(6L_0+12d+3)$
-- statement:
--   Suppose we have algorithmic access to $(X,Y)$ with $\Delta[X],\Delta[Y]\le L_0$, and let $d=d[X;Y]$. Fix one of the five families, let $(X',Y')$ be obtained by applying it to $(X,Y)$, and let $(\hat X,\hat Y)$ be obtained by bucketing $(X',Y')$. Then
--   $$\mathbb E_{Z,J_X,J_Y}\bigl[\Phi_{X,Y}(\hat X,\hat Y)\bigr]\le\mathbb E_Z\bigl[\Phi_{X,Y}(X',Y')\bigr]+2\log(6L_0+12d+3),$$
--   where $J_X,J_Y$ are the bucketing labels and $Z$ is the fiber label of the family.
--
--   The claim says that bucketing is cheap from the entropic point of view.
--
--   Differences from the source:
--
--   - reading: E_{J_X,J_Y} on the left → E over Z, J_X and J_Y; reason: the printed proof fixes Z = z and averages over Z in Eq. (41)
--   - generalization: η the constant of Theorem 4.3 → every η ∈ (0, 1] and every real L₀; reason: the proof uses only (1 + η)/2 ≤ 1; the constant of Theorem 4.3 can be taken in (0, 1)
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Claim 4.10, p.30

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Claim 4.10.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.30: for access to `(X, Y)` with `Δ[X], Δ[Y] ≤ L₀`, `d := d[X;Y]`, any of the
five families `f`, its output `(X′, Y′)` and the buckets `(X̂, Ŷ)` of `(X′, Y′)`:
`E[Φ_{X,Y}(X̂, Ŷ)] ≤ E_Z[Φ_{X,Y}(X′, Y′)] + 2 log (6L₀ + 12d + 3)`.

**Formalization Note.** The left side also averages over the fiber labels `Z`: the proof fixes `Z = z`,
then averages in (41). The printed subscript `J_X, J_Y` omits `Z`. The claim holds for every
`η ∈ (0, 1]` and every `L₀`; it does not use the decrement. -/
theorem claim_4_10_bucketing_potential {n : ℕ} (η L₀ : ℝ) (h0 : 0 < η) (h1 : η ≤ 1)
    (s : AccessState n) (hX : IsAccess s.X s.MX) (hY : IsAccess s.Y s.MY)
    (hΔX : slack s.X s.MX ≤ L₀) (hΔY : slack s.Y s.MY ≤ L₀) (f : Family) :
    expect (familyOutcomeLaw f s) (fun ω =>
        potential η s.X.sample s.Y.sample (nextState f s ω).X.sample (nextState f s ω).Y.sample) ≤
      expect (familyLabel f s.X.sample s.Y.sample) (fun ℓ =>
          potential η s.X.sample s.Y.sample (applyFamily f s ℓ).X.sample
            (applyFamily f s ℓ).Y.sample) +
        ENNReal.ofReal (2 * Real.logb 2 (6 * L₀ + 12 * s.dist + 3)) := by sorry

end AlgoPFR
