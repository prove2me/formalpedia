-- Prove2me | Theorems.Thm_ConnesRZ_spectral_weil_pair_hasSum
-- name    : ConnesRZ.spectral_weil_pair_hasSum
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T15:01:48.728826+00:00
-- url     : https://prove2.me/theorems/fb1c40c9-2159-495d-9814-562fc21dfa56
-- title:
--   Polarized Connes explicit formula for a C² factor and a continuous factor
-- statement:
--   Let $f:\mathbb R\to\mathbb C$ be twice continuously differentiable with compact support, and let $g:\mathbb R\to\mathbb C$ be continuous with compact support. Over the actual critical-strip zeta zeros with analytic multiplicities, the family below has unconditional sum
--   $$\sum_\rho m_\rho\widehat f(\rho)\,\overline{\widehat g(1-\bar\rho)}=W(f\star g^*).$$
--   The first factor supplies the C² regularity of the convolution; the second requires only continuity. The transforms, Weil distribution, zero subtype and multiplicities are those of the original Connes development. No extra summability or explicit-formula assumption remains.
-- source:
--   Connes, Noncommutative geometry and the Riemann zeta function, section 3, eqs. (11)-(12). Zeta23 ExplicitFormula.lean, paperFT_weilTest and weilTest_contDiff (Appendix A normalization), anthropics/formal-math e1a4e6508154ea59f030480661590a9fe3018011. Certified mixed normalization and actual-zero transport in monocap-tech/weil branch audit/explicit-formula-bridge, PolarizedExplicitFormula.lean, following compiling commit 4383bf3549a77d9b83022541eec8845dc942c3a8.

import Definitions.Def_ConnesRZ_weil_defs
open Complex MeasureTheory Set

theorem ConnesRZ.spectral_weil_pair_hasSum (f g : ℝ → ℂ) (hf : ContDiff ℝ 2 f)
    (hg : Continuous g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // IsCriticalZero s} =>
      (zeroMult ρ.1 : ℂ) * (mellinHat f ρ.1 *
        (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1))))
      (weilDistribution (conv f (starInv g))) := by sorry
