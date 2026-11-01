-- Prove2me | Theorems.Thm_AllPhotonicRepeater_exists_tree_zx_success_poly_size
-- name    : AllPhotonicRepeater.exists_tree_zx_success_poly_size
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:22:11.413118+00:00
-- url     : https://prove2.me/theorems/aa75db4c-e997-4c9e-aedc-ac814f7984ca
-- title:
--   p. 7 claim with (A4), and (A13), (A16): $P_Z,P_X\ge1-\delta$ with a tree of size polynomial in $1/\delta$
-- statement:
--   Let $0\le\epsilon_0<1/2$. There are constants $C$ and $k\in\mathbb N$ such that for every $\delta$ with $0<\delta\le1$ there is a tree cluster state, with depth index $l\ge1$ and branching parameters $b_i\ge1$ for $i\le l$, whose loss-tolerant $Z$- and $X$-measurements fail with probability at most $\delta$ and whose size is polynomial in $1/\delta$:
--   $$
--   1-P_Z\le\delta,\qquad 1-P_X\le\delta,\qquad Q_L\le C\Big(\frac1\delta\Big)^{k}.
--   $$
--   The constants $C$ and $k$ depend on $\epsilon_0$ only.
--
--   The paper states that the success probability of the loss-tolerant measurement "can be made arbitrary close to unity, as long as $\epsilon_0<0.5$", and quotes a numerical fit (A4) for the tree size. This item is the exact property of $P_Z$ and $P_X$ that the scaling argument of App. C1 needs: it is the step at which the threshold $\epsilon_0<1/2$ enters.
--
--   Differences from the source:
--   - reading: $P_L$ can be made arbitrarily close to 1 for $\epsilon_0<0.5$, with $Q_L\simeq(\ln 1/(1-P_L))^{4.5}$ (numerical, (A4)) → for $\epsilon_0<1/2$, $P_Z$ and $P_X$ are $\ge1-\delta$ for a tree with $Q_L\le C(1/\delta)^k$; reason: (A4) is a numerical fit cited from [27, 41], not a mathematical statement of this paper; the milestone states the property of $P_Z$ (A13) and $P_X$ (A16) that (C1) uses
--   - reading: (A3) printed for $1\le k\le l$ → $R_k$ given by (A3) also at $k=0$; reason: (A16) reads $P_X=R_0$, and (A7), (A9), (A12) give $R_k=1-(1-S_k)^{b_k}$ at every level, $k=0$ included
--   - encoding: $R_{l+1}:=0$ and $b_{l+1}:=0$ → $R_k=0$ and $b_k$ read as $0$ for every $k>l$; reason: $R_{l+2}$ enters only $R_l$, raised to the power $b_{l+1}=0$, so its value never matters; same instances
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A1, text around Eq. (A4), p. 7; App. A2, Eqs. (A13), (A16) and the sentence after (A17), p. 9

import Mathlib
import Definitions.Def_AllPhotonicRepeater_treeSize
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. A1, p. 7 (the
claim around Eq. (A4)) with App. A2, Eqs. (A13), (A16), p. 9: for every per-photon loss
probability `0 ≤ ε0 < 1/2` there are constants `C` and `k` such that for every target failure
probability `0 < δ ≤ 1` some tree (depth index `l ≥ 1`, every branching `b_i ≥ 1` for `i ≤ l`)
has loss-tolerant `Z`- and `X`-measurement failure probabilities `1 − P_Z ≤ δ`, `1 − P_X ≤ δ`
with size `Q_L ≤ C (1/δ)^k`.

**Formalization Note** The page says the success probability can be made arbitrarily close to
unity as long as `ε0 < 0.5`, with `Q_L ≃ (ln 1/(1 − P_L))^{4.5}` "numerically shown [27, 41]".
That fit is not a mathematical statement of the paper; this item states the exact property of
`P_Z` (A13) and `P_X` (A16) that the App. C1 scaling argument uses. `C` and `k` are chosen
after `ε0` and before `δ`. A two-level tree suffices: with `r = ε0/(1 − ε0) < 1`, choose `b_1`
with `r^{b_1+1}(ln(1/δ) + 1) ≤ δ/2` and `b_0 ≈ (ln(1/δ) + 1)/(1 − ε0)^{b_1+1}`. -/
theorem exists_tree_zx_success_poly_size (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 < 1 / 2) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ l : ℕ, ∃ b : ℕ → ℕ, 1 ≤ l ∧ (∀ i ≤ l, 1 ≤ b i) ∧
        1 - zSuccess ε0 l b ≤ δ ∧ 1 - xSuccess ε0 l b ≤ δ ∧
        (treeSize l b : ℝ) ≤ C * (1 / δ) ^ k := by sorry

end AllPhotonicRepeater
