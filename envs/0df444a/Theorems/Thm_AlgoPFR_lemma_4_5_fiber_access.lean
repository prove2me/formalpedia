-- Prove2me | Theorems.Thm_AlgoPFR_lemma_4_5_fiber_access
-- name    : AlgoPFR.lemma_4_5_fiber_access
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:26.990448+00:00
-- url     : https://prove2.me/theorems/22de8592-ffda-4cc5-809f-21d779804956
-- title:
--   Lemma 4.5 — access to the fiber $X_z=(X\mid X+Y=z)$
-- statement:
--   Suppose we have algorithmic access to independent $X,Y$ with envelopes $M_X,M_Y$, and let $Z=X+Y$. For every $z\in\mathrm{supp}(Z)$ the fiber protocol constructs algorithmic access to $X_z=(X\mid Z=z)$ with envelope $M_{X_z}=M_XM_Y/p_Z(z)$. One trial of its sampler is accepted with probability $p_Z(z)/M_Y$, so the expected number of trials is $M_Y/p_Z(z)$.
--
--   If the label is drawn as $z\sim X+Y$, then
--   $$\mathbb E_{z\sim Z}\,\Delta(X_z)=\Delta[X]+\Delta[Y],$$
--   $$\mathbb E_{z\sim Z}\log\frac{M_Y}{p_Z(z)}=H[X+Y]+\log M_Y\le\Delta[Y]+2\,d[X;Y].$$
--
--   Rejection appears here, which is why the cost of an access procedure can blow up along a trajectory.
--
--   Differences from the source:
--
--   - reading: "algorithmic access" of Definition 4.1, including expected poly(n, K) time → the sampler law, the coin rate and the envelope, with trial and parent-call counts in place of time; reason: the lemma's own trial count M_Y / p_Z(z) is not polynomial for rare z
--   - generalization: no per-trial call counts in the printed statement → one trial and one coin each make exactly two parent calls; reason: read off the printed proof; the printed claim follows by dropping these clauses
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 4.5, p.21

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 4.5.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.21: from access to independent `X, Y` and `Z := X + Y`, for every
`z ∈ supp(Z)` the fiber protocol constructs access to `X_z := (X | Z = z)` with envelope
`M_X M_Y / p_Z(z)`; one trial is accepted with probability `p_Z(z) / M_Y`, so the expected number of
trials is `M_Y / p_Z(z)`. If `z ∼ X + Y` then `E[Δ(X_z)] = Δ[X] + Δ[Y]` (13) and
`E[log (M_Y / p_Z(z))] = H[X + Y] + log M_Y ≤ Δ[Y] + 2 d[X;Y]` (14).

**Formalization Note.** Expectations over `z` are finite real sums; the terms with `p_Z(z) = 0` vanish
whatever the junk value of the fiber at `z`. Call counts are read off the proof: two parent calls per
trial and two per coin. -/
theorem lemma_4_5_fiber_access {n : ℕ} (X Y : Oracle n) (MX MY : ℝ) (hX : IsAccess X MX)
    (hY : IsAccess Y MY) :
    (∀ z, 0 < sumMass X Y z →
      (fiberOracle X Y z).sample = fiberLaw X.sample Y.sample z ∧
        IsAccess (fiberOracle X Y z) (MX * MY / sumMass X Y z) ∧
        ((fiberTrial X Y z).law none).toReal = 1 - sumMass X Y z / MY ∧
        expectedTrials (fiberTrial X Y z).law = ENNReal.ofReal (MY / sumMass X Y z) ∧
        (fiberTrial X Y z).UsesCalls 2 ∧ ∀ x, (fiberCoinProc X Y z x).UsesCalls 2) ∧
      ∑ z, sumMass X Y z * slack (fiberOracle X Y z) (MX * MY / sumMass X Y z) =
        slack X MX + slack Y MY ∧
      ∑ z, sumMass X Y z * Real.logb 2 (MY / sumMass X Y z) =
        entropy (sumLaw X.sample Y.sample) + Real.logb 2 MY ∧
      entropy (sumLaw X.sample Y.sample) + Real.logb 2 MY ≤
        slack Y MY + 2 * rd X.sample Y.sample := by sorry

end AlgoPFR
