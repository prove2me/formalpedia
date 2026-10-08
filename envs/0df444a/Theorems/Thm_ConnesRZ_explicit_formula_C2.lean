-- Prove2me | Theorems.Thm_ConnesRZ_explicit_formula_C2
-- name    : ConnesRZ.explicit_formula_C2
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T14:38:21.960651+00:00
-- url     : https://prove2.me/theorems/f873c99e-ea18-498b-8de0-cc2ecce9d785
-- title:
--   Connes explicit formula for C² compactly supported tests
-- statement:
--   For every twice continuously differentiable compactly supported $g:\mathbb R\to\mathbb C$, the actual critical-strip zeta zeros with their analytic multiplicities satisfy the Connes explicit formula as an unconditional sum:
--
--   $$\sum_{\rho:\,\zeta(\rho)=0,\,0<\operatorname{Re}\rho<1}m_\rho\,\widehat g(\rho)=W(g),\qquad
--   \widehat g(s)=\int_{\mathbb R}g(t)e^{(s-1/2)t}\,dt.$$
--
--   Here $W(g)$ uses the original pole, prime-power, and archimedean terms. This exposes the regularity already supported by the proved literature explicit formula. No explicit-formula premise or seam parameter remains, and the existing smooth-test predicate and theorem are unchanged.
-- source:
--   Connes, Noncommutative geometry and the Riemann zeta function, section 3, eqs. (11)-(12), pp. 15-16; Zeta23/ExplicitFormula.lean EF_lit and WeilEF/Main.lean EF_lit_zeta from anthropics/formal-math e1a4e6508154ea59f030480661590a9fe3018011. Certified cross-interface transport in monocap-tech/weil branch audit/explicit-formula-bridge, ExplicitFormulaBridge.lean; prior compiling commit 1e0a38742c9a5ecd976ba439f188cb3f5fa66e37. Current C2 theorem adds an interface without changing IsTest or the existing smooth-test theorem.

import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ExplicitFormula
open Complex MeasureTheory ConnesRZ

theorem ConnesRZ.explicit_formula_C2 (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1) (weilDistribution g) := by sorry
