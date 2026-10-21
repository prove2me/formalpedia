-- Prove2me | Theorems.Thm_CostlyShort_OneAsset_prop3_unique_positive_root
-- name    : CostlyShort.OneAsset.prop3_unique_positive_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:35.305863+00:00
-- url     : https://prove2.me/theorems/a46c9ef4-05bf-4af6-baba-5cb7b9acc54a
-- title:
--   Proof of Proposition 3, p. 50 — for s > s*, (30) has a unique strictly positive solution
-- statement:
--   Let $\sigma>0$, $s\in(0,1)$ and $\Delta\in\mathbb R$ with $\sigma<s\Delta$, i.e. the optimist's consumption share lies in the shorting region $s>s^*$. Then the quadratic
--   $$
--   g(\gamma)=(1-s)(s\Delta-\gamma-\sigma)\big((\gamma+\Delta)s-\sigma\big)-\gamma\sigma(1+s)^2
--   $$
--   has exactly one strictly positive root:
--   $$
--   \exists!\,\gamma>0:\quad g(\gamma)=0 .
--   $$
--
--   Together with the equivalence between (30) and $g(\gamma)=0$, this says that on the shorting region the lending-yield equation of the one-asset economy has a unique strictly positive solution.
--
--   **Formalization Note** $s>s^*=\min\{1,\sigma/\Delta\}$ with $s<1$ is encoded as $\sigma<s\Delta$, which avoids the junk value $\sigma/0=0$.
-- source:
--   Evgeniou, Hugonnier & Prieto, Asset Pricing with Costly Short Sales, SFI Research Paper N°22-21 (version of September 22, 2022), App. A, proof of Proposition 3, p. 50 ("it is clear that (30) admits a unique strictly positive solution")

import Mathlib
import Definitions.Def_CostlyShort_OneAsset_Setting

namespace CostlyShort.OneAsset

theorem prop3_unique_positive_root (σ s Δ : ℝ) (hσ : 0 < σ) (hs0 : 0 < s) (hs1 : s < 1)
    (hreg : σ < s * Δ) :
    ∃! γ : ℝ, 0 < γ ∧ gQuad σ Δ s γ = 0 := by sorry

end CostlyShort.OneAsset
