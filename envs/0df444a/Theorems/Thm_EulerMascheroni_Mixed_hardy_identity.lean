-- Prove2me | Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
-- name    : EulerMascheroni.Mixed.hardy_identity
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T12:47:42.563624+00:00
-- url     : https://prove2.me/theorems/b9a24cdc-07eb-4972-b94e-b2ad36463593
-- title:
--   Hardy identity relating Ein(1), Euler’s constant, and Gompertz’s constant
-- statement:
--   With the entire function $\operatorname{Ein}$ and the integral constant $\delta$ from the shared definition, the classical identity is
--
--   $$\operatorname{Ein}(1)=\gamma+\frac\delta e.$$
--
--   This is a known analytic identity, independent of all transcendence conjectures. It supplies the exact algebraic relation needed to connect Euler's constant to the mixed-function family. This node is an open formalization task, not an open mathematical conjecture.
-- source:
--   S. Fischler and T. Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, J. Number Theory 261 (2024), 36–54; author manuscript https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Definition 1 and Conjecture 3 (pp. 5–6), Theorem 4 (p. 6), and Eq. (4.5) (p. 14). Eq. (4.5), equivalently §4.4: e E_{1,2}(-1)-e gamma=delta, with E_{1,2}(-1)=Ein(1) by shifting the series index.

import Definitions.Def_eulerMascheroni_mixedCover

theorem EulerMascheroni.Mixed.hardy_identity :
    EulerMascheroni.Mixed.ein 1 = (Real.eulerMascheroniConstant : ℂ) +
      (EulerMascheroni.gompertzConstant : ℂ) / Complex.exp 1 := by sorry
