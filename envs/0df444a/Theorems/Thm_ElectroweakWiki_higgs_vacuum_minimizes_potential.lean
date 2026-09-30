-- Prove2me | Theorems.Thm_ElectroweakWiki_higgs_vacuum_minimizes_potential
-- name    : ElectroweakWiki.higgs_vacuum_minimizes_potential
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:19:59.430711+00:00
-- url     : https://prove2.me/theorems/4f35dfa2-889a-45ed-9bb9-c6056a468364
-- title:
--   The Higgs vacuum minimizes $\lambda(|h|^2 - v^2/2)^2$
-- statement:
--   Let $\lambda>0$ and $v\in\mathbb R$, and let $V(h) = \lambda\,(|h|^2 - v^2/2)^2$ be the Higgs potential on complex doublets $h\in\mathbb C^2$, with $|h|^2 = |h_1|^2+|h_2|^2$. Let $h_0 = (0, v/\sqrt2)$. Then
--
--   1. $|h_0|^2 = v^2/2$;
--   2. $V(h_0) = 0$;
--   3. $V(h_0)\le V(h)$ for every $h$;
--   4. $V(h) = 0$ exactly when $|h|^2 = v^2/2$.
--
--   This justifies calling $v$ the vacuum expectation value in $\mathcal L_h$, and it identifies $h_0$ as a vacuum.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; Section 'Before electroweak symmetry breaking', L_h = |D_μ h|² − λ(|h|² − v²/2)², 'where v is the vacuum expectation value' (p. 4 of the PDF)

import Definitions.Def_ElectroweakWiki_defs
open Matrix

namespace ElectroweakWiki

theorem higgs_vacuum_minimizes_potential (lam v : ℝ) (hlam : 0 < lam) :
    doubletNormSq (higgsVacuum v) = v ^ 2 / 2 ∧
      higgsPotential lam v (higgsVacuum v) = 0 ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v (higgsVacuum v) ≤ higgsPotential lam v h) ∧
      (∀ h : Fin 2 → ℂ, higgsPotential lam v h = 0 ↔ doubletNormSq h = v ^ 2 / 2) := by sorry

end ElectroweakWiki
