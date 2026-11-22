-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_comp_add
-- name    : FiniteEnergyPlane.dlambdaEnergy_comp_add
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-22T19:07:29.947956+00:00
-- url     : https://prove2.me/theorems/7d42d3d0-dec9-4c2a-ac94-bc20873d6ad8
-- title:
--   The dλ-energy under a translation of the domain
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n}$ and $B\in\mathbb{C}$. For every set $s\subseteq\mathbb{C}$, the $d\lambda$-energy of $z\mapsto u(z+B)$ on $s$ equals the $d\lambda$-energy of $u$ on the translate $s+B$:
--   $$\int_s (u(\cdot+B))^*d\lambda=\int_{s+B}u^*d\lambda .$$
--
--   This is the translation counterpart of the dilation identity for the $d\lambda$-energy; together they describe how the $d\lambda$-energy transforms under complex affine reparametrizations $z\mapsto Az+B$ of a plane. It is used for comparing normalized fast planes that differ by such a reparametrization (Hryniewicz 2012, Section 7).
--
--   **Formalization Note** The $d\lambda$-energy is `dlambdaEnergy H s u = ∫⁻ z in s, ENNReal.ofReal (dlambdaDensity H u z)`, so only the positive part of the density is counted; no measurability or regularity of $s$ or $u$ is assumed. The translate is the image `(fun y => y + B) '' s`.
-- source:
--   General lemma; used toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, arXiv:0812.4076, Lemma 7.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `B ∈ ℂ` and `u : ℂ → V n`. For every `s ⊆ ℂ`, the `dλ`-energy of `z ↦ u (z + B)` on `s`
equals the `dλ`-energy of `u` on the translate `s + B`. -/
theorem dlambdaEnergy_comp_add {n : ℕ} (H : V n → ℝ) (u : ℂ → V n) (B : ℂ) (s : Set ℂ) :
    dlambdaEnergy H s (fun z => u (z + B)) = dlambdaEnergy H ((fun y => y + B) '' s) u := by
  sorry

end FiniteEnergyPlane
