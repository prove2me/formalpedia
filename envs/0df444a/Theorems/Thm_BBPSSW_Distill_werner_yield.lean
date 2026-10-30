-- Prove2me | Theorems.Thm_BBPSSW_Distill_werner_yield
-- name    : BBPSSW.Distill.werner_yield
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:46:10.550876+00:00
-- url     : https://prove2.me/theorems/56d51e7f-5557-41a3-b74f-6e3d78752f3f
-- title:
--   Werner breeding yield, Eq. (8) (corrected: threshold 0.8107 → exact root F* ∈ (0.8107, 0.8108))
-- statement:
--   1. For every $0\le F\le1$,
--
--   $$1-S(W_F)=1+F\log_2F+(1-F)\log_2\frac{1-F}{3}.$$
--
--   2. There is $F^*\in(0.8107,\,0.8108)$ such that, for $0\le F\le1$, this yield is positive if and only if $F>F^*$.
--
--   The paper prints "positive for $F>0.8107$". The root is $F^*=0.810710375\ldots$, so the printed threshold is a rounding: at $F=0.81071$ the yield is about $-1.38\times10^{-6}$. Breeding alone therefore distills Werner states exactly when $F>F^*$; for $\tfrac12<F\le F^*$ the recurrence step first raises $F$ above $F^*$.
--
--   Differences from the source:
--   - correction: the yield (8) is positive for F > 0.8107 → the yield is positive iff F > F* for some F* ∈ (0.8107, 0.8108); reason: false as printed: F = 0.81071 satisfies F > 0.8107 and 0 ≤ F ≤ 1, yet 1 + F log2 F + (1−F) log2((1−F)/3) ≈ −1.38 × 10⁻⁶ < 0; the root is 0.810710375…
--   - encoding: 1 − S(W_F) for Werner states → stated for 0 ≤ F ≤ 1, entropy in bits with 0 log 0 = 0; reason: W_F is a state exactly for these F
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (8), p. 3

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_vnEntropy
import Definitions.Def_BBPSSW_Distill_wernerState
import Definitions.Def_BBPSSW_Distill_wernerYield

open ShadowTomography.QuantumLB (vnEntropy)

namespace BBPSSW.Distill

/-- **The breeding yield of Werner states, Eq. (8) (corrected threshold).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (8), p. 3: "For Werner states the yield
1 − S(WF) = 1 + F log2 F + (1−F) log2 ((1−F)/3) (8)
is positive for F > 0.8107."

1. For every `0 ≤ F ≤ 1`, `1 − S(W_F) = 1 + F log₂ F + (1 − F) log₂((1 − F)/3)`.
2. There is `F* ∈ (0.8107, 0.8108)` such that for `0 ≤ F ≤ 1` the yield is positive if and
   only if `F > F*`.

**Formalization Note.** The printed threshold is a rounding: the yield vanishes at
`F* = 0.810710375…`, and at `F = 0.81071` (which satisfies "F > 0.8107") it is
`≈ −1.38 × 10⁻⁶ < 0`. The statement gives the exact threshold as an iff, located in
`(0.8107, 0.8108)`. Entropy is in bits with `0 log 0 = 0`. -/
theorem werner_yield :
    (∀ F : ℝ, 0 ≤ F → F ≤ 1 → 1 - vnEntropy (wernerState F) = wernerYield F) ∧
      ∃ Fstar : ℝ, 0.8107 < Fstar ∧ Fstar < 0.8108 ∧
        ∀ F : ℝ, 0 ≤ F → F ≤ 1 → (0 < wernerYield F ↔ Fstar < F) := by sorry

end BBPSSW.Distill
