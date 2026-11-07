-- Prove2me | Theorems.Thm_AlgoPFR_lemma_4_6_endgame_access
-- name    : AlgoPFR.lemma_4_6_endgame_access
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:27.113686+00:00
-- url     : https://prove2.me/theorems/8970bebb-aab0-4a3e-bda5-f5f9efbc28b2
-- title:
--   Lemma 4.6 — access to the endgame law $U_{z,w}$
-- statement:
--   Suppose we have algorithmic access to $X,Y$ with envelopes $M_X,M_Y$. Let $X_0,X_1,Y_0,Y_1$ be independent copies, $Z=X_1+Y_0$, $S=X_0+Y_1$, $W=Z+S$. For $(z,w)\in\mathrm{supp}(Z,W)$ let $s=z+w$ and $U_{z,w}=(X_1+Y_1\mid Z=z,W=w)$. The endgame protocol constructs exact algorithmic access to $U_{z,w}$ with envelope $M_XM_Y/p_{X+Y}(s)$, using two fiber rejection samplers, with trial acceptance probabilities $p_{X+Y}(z)/M_Y$ and $p_{X+Y}(s)/M_X$. For $(z,w)$ drawn from the natural law of $(Z,W)$,
--   $$\mathbb E\,\Delta[U_{z,w}]\le\Delta[X]+\Delta[Y]+4\,d[X;Y],$$
--   $$\mathbb E\Bigl[\log\frac{M_Y}{p_{X+Y}(z)}+\log\frac{M_X}{p_{X+Y}(w+z)}\Bigr]=\Delta[X]+\Delta[Y]+2\,d[X;Y].$$
--
--   This completes the access layer for the five GGMT operations.
--
--   Differences from the source:
--
--   - reading: "exact algorithmic access" of Definition 4.1, including expected poly(n, K) time → the sampler law, the coin rate and the envelope, with the two trial acceptance probabilities; reason: the time clause fails on rare labels, as for Lemma 4.5
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 4.6, p.22

import Mathlib
import Definitions.Def_AlgoPFR_Iteration

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 4.6.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.22: for `(z, w) ∈ supp(Z, W)` with `Z := X₁ + Y₀`, `S := X₀ + Y₁`,
`W := Z + S`, `s := z + w`, the endgame protocol constructs exact access to
`U_{z,w} := (X₁ + Y₁ | Z = z, W = w)` with envelope `M_X M_Y / p_{X+Y}(s)`; it uses two fiber rejection
samplers with trial acceptance probabilities `p_{X+Y}(z) / M_Y` and `p_{X+Y}(s) / M_X`. For `(z, w)`
from the natural law of `(Z, W)`, `E Δ[U_{z,w}] ≤ Δ[X] + Δ[Y] + 4 d[X;Y]` (16) and
`E[log (M_Y / p_{X+Y}(z)) + log (M_X / p_{X+Y}(w + z))] = Δ[X] + Δ[Y] + 2 d[X;Y]` (17).

**Formalization Note.** Eq. (17) is an equality as printed (the printed proof writes `≤`; equality
holds). The second acceptance probability is that of `fiberTrial Y X s`, whose mass `p_{Y+X}(s)` equals
`p_{X+Y}(s)`; the theorem states it with `p_{X+Y}` as printed. -/
theorem lemma_4_6_endgame_access {n : ℕ} (X Y : Oracle n) (MX MY : ℝ) (hX : IsAccess X MX)
    (hY : IsAccess Y MY) :
    (∀ z w, (z, w) ∈ (endgameLabel X.sample Y.sample).support →
      (endgameOracle X Y z (z + w)).sample = endgameLaw X.sample Y.sample z w ∧
        IsAccess (endgameOracle X Y z (z + w)) (MX * MY / sumMass X Y (z + w)) ∧
        ((fiberTrial X Y z).law none).toReal = 1 - sumMass X Y z / MY ∧
        ((fiberTrial Y X (z + w)).law none).toReal = 1 - sumMass X Y (z + w) / MX) ∧
      ∑ ℓ : Vec n × Vec n, ((endgameLabel X.sample Y.sample) ℓ).toReal *
          slack (endgameOracle X Y ℓ.1 (ℓ.1 + ℓ.2)) (MX * MY / sumMass X Y (ℓ.1 + ℓ.2)) ≤
        slack X MX + slack Y MY + 4 * rd X.sample Y.sample ∧
      ∑ ℓ : Vec n × Vec n, ((endgameLabel X.sample Y.sample) ℓ).toReal *
          (Real.logb 2 (MY / sumMass X Y ℓ.1) + Real.logb 2 (MX / sumMass X Y (ℓ.2 + ℓ.1))) =
        slack X MX + slack Y MY + 2 * rd X.sample Y.sample := by sorry

end AlgoPFR
