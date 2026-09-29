-- Prove2me | Theorems.Thm_ElectroweakWiki_electric_charge_unbroken
-- name    : ElectroweakWiki.electric_charge_unbroken
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:33:08.909976+00:00
-- url     : https://prove2.me/theorems/336acd47-e882-407d-9936-c36dbaf4a11f
-- title:
--   $Q = T_3 + \frac12 Y$ does not couple to the Higgs vacuum
-- statement:
--   Let $v\neq 0$ and $h_0 = (0, v/\sqrt2)$. On the Higgs doublet (hypercharge $Y=1$, isospin $T_3 = \sigma_3/2$) the combination $aT_3 + bY/2$ acts as the matrix $\frac a2\sigma_3 + \frac b2\mathbb 1$. Then
--
--   1. the charge generator $Q = T_3 + \frac12 Y$ (that is $a=b=1$) annihilates $h_0$;
--   2. the lower component of the doublet has charge $Q(-\tfrac12, 1) = -\tfrac12 + \tfrac12 = 0$;
--   3. for real $a, b$, the generator $aT_3 + bY/2$ annihilates $h_0$ if and only if $a = b$.
--
--   So, up to scale, $Q$ is the only combination of $T_3$ and $Y$ that does not couple to the vacuum; any other combination acts nontrivially on it. This is the sense in which $\mathrm U(1)_{em}$ is unbroken.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section Formulation, 'The electric charge arises as the particular linear combination (nontrivial) of YW and T3 (Q = T3 + ½YW) that does not couple to the Higgs boson ... while any other combination of the hypercharge and the weak isospin must interact with the Higgs' and 'U(1)em ... is unbroken' (pp. 2–3 of the PDF)

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem electric_charge_unbroken (v : ℝ) (hv : v ≠ 0) :
    isospinHyperchargeGenerator 1 1 *ᵥ higgsVacuum v = 0 ∧
      electricCharge (-1 / 2) 1 = 0 ∧
      (∀ a b : ℝ, isospinHyperchargeGenerator a b *ᵥ higgsVacuum v = 0 ↔ a = b) := by sorry

end ElectroweakWiki
