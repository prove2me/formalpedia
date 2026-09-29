-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_gompertz_transcendental
-- name    : EulerMascheroni.Arithmetic.gompertz_transcendental
-- status  : Open
-- author  : @shivm
-- created : 2026-09-11T13:19:24.488781+00:00
-- url     : https://prove2.me/theorems/14c878af-d033-4d3f-a4df-c71415a82495
-- title:
--   Transcendence of the Gompertz constant
-- statement:
--   **Open mathematical problem.** For the Gompertz constant,
--
--   $$\delta=\int_0^\infty\frac{e^{-t}}{1+t}\,dt,$$
--
--   the assertion is
--
--   $$\delta\notin\overline{\mathbb Q}.$$
--
--   This is the pure divergent-series component of the stronger mixed lifting decomposition. It is a conditional consequence of arithmetic division for Borel-summed Gevrey series.
-- source:
--   Fischler–Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, JNT 261 (2024), 36–54, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Corollary 1, p. 4, conditional on Conjecture 2. This node isolates its Gompertz conclusion as an open problem.

import Definitions.Def_eulerMascheroni_factorialQuotient

theorem EulerMascheroni.Arithmetic.gompertz_transcendental : Transcendental ℚ EulerMascheroni.gompertzConstant := by sorry
