-- Prove2me | Theorems.Thm_ConnesRZ_actual_zero_reciprocal_square_summable
-- name    : ConnesRZ.actual_zero_reciprocal_square_summable
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T23:24:36.289173+00:00
-- url     : https://prove2.me/theorems/de16ef44-c04f-4b8a-ba99-8107f9af4d39
-- title:
--   Multiplicity-weighted reciprocal-square summability for all actual critical-strip zeta zeros
-- statement:
--   Let $Z=\{\rho\in\mathbb C:\zeta(\rho)=0,\ 0<\operatorname{Re}\rho<1\}$ and let $m_\rho$ be the analytic multiplicity of the actual Riemann-zeta zero $\rho$. Then the nonnegative family
--   $$ \left(\frac{m_\rho}{1+|\gamma_\rho|^2}\right)_{\rho\in Z},\qquad \gamma_\rho=\frac{\rho-1/2}{i}, $$
--   is unconditionally summable. The carrier is the full set of actual critical-strip zeros, all analytic multiplicities are retained, and no RH, positivity, abstract-zero-configuration, or zero-count assumption appears in the statement.
--
--   This is the summable majorant used by the independently checked Connes–Weil Green-column frontier to control all high-ordinate actual Green reciprocals. The proof uses the already proved actual-zeta unit-window count, while the physical Green metric realization remains a separate obligation.
-- source:
--   Anthropic formal-math e1a4e6508154ea59f030480661590a9fe3018011, zeta23/Zeta23/WeilEF/ZeroSummability.lean, zero_sum_inv_sq_gen and zero_sum_inv_sq; reused with license and exact carrier/multiplicities in monocap-tech/weil, WeilDefect/Connes/ActualGreenSummability.lean, actual_zero_reciprocal_square_summable. Local-count prerequisite: https://prove2.me/theorems/2abaa392-a81f-480c-8c0f-d476f67838ae .
--
--   Literature/source audit addendum (2026-10-11): The exact unchanged native theorem is WeilDefect.ConnesNative.actual_zero_reciprocal_square_summable. The ConnesRZ graph name is a recovered named export, rather than a literal declaration in ActualGreenSummability.lean. The exact graph type was independently checked in Lean, preserving the actual zeta-zero carrier and multiplicities.
--
--   Literature/source audit addendum (2026-10-11; COR-15): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil d73d0e7f1477c934a3a8f8b01012852128b977bb, WeilDefect/Connes/ActualGreenSummability.lean, SHA256 0d1e244e5579f71293661e2d83f397f44faafcb11348a0ad15583ac407b9b8c0. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry.

import Mathlib
import Definitions.Def_ConnesRZ_weil_defs

theorem ConnesRZ.actual_zero_reciprocal_square_summable : Summable (fun ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} =>
      (ConnesRZ.zeroMult ρ.1 : ℝ) / (1 + Complex.normSq ((ρ.1 - 1 / 2) / Complex.I))) := by sorry
