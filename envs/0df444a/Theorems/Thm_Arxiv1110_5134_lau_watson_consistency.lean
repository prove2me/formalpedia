-- Prove2me | Theorems.Thm_Arxiv1110_5134_lau_watson_consistency
-- name    : Arxiv1110_5134.lau_watson_consistency
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:20:22.81781+00:00
-- url     : https://prove2.me/theorems/f9ccb8b3-bb51-45f6-aeab-2ab6d4083ca5
-- title:
--   Eqs. (73)-(74): the transport operator agrees with Lau and Watson's
-- statement:
--   Let $n(s)>0$ and the Stokes vector $\mathbf I(s)$ be differentiable at $s$. Let $\kappa_e$ be a scalar extinction coefficient and $\mathbf R$ the torsion matrix of Eq. (14). Then (Eq. 73)
--
--   $$-\frac{d}{ds}\ln n^2=\frac{d}{ds}\ln\frac1{n^2}=n^2\frac{d}{ds}\Big(\frac1{n^2}\Big),$$
--
--   and Lau and Watson's transport operator (Eqs. 71-72), with $1/L=1/l-\frac{d}{ds}\ln n^2$ and $1/l=\kappa_e$, equals the transport operator of Eq. (20) with scalar extinction (Eq. 74):
--
--   $$\frac{d\mathbf I}{ds}+\Big(\kappa_e-\frac{d}{ds}\ln n^2\Big)\mathbf I+\mathbf R\mathbf I=n^2\frac{d}{ds}\Big[\frac{\mathbf I}{n^2}\Big]+(\kappa_e+\mathbf R)\mathbf I.$$
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c031; Section 3.2 (text after Eq. 21) and Appendix B, Eqs. (71)-(74), PDF pp. 12, 26-27

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem lau_watson_consistency (n : ℝ → ℝ) (S : ℝ → Stokes) (s ke κ : ℝ)
    (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s) (hS : DifferentiableAt ℝ S s) :
    -deriv (fun t => Real.log (n t ^ 2)) s = deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s ∧
    deriv (fun t => Real.log ((n t ^ 2)⁻¹)) s = n s ^ 2 * deriv (fun t => (n t ^ 2)⁻¹) s ∧
    deriv S s + (ke - deriv (fun t => Real.log (n t ^ 2)) s) • S s + rytovMatrix κ *ᵥ S s =
      transportOp n S s + (ke • (1 : Matrix (Fin 4) (Fin 4) ℝ) + rytovMatrix κ) *ᵥ S s := by sorry

end Arxiv1110_5134
