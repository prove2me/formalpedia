-- Prove2me | Theorems.Thm_Arxiv1503_02159_phaseless_global_uniqueness
-- name    : Arxiv1503_02159.phaseless_global_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T13:38:36.56966+00:00
-- url     : https://prove2.me/theorems/ecfb319b-b78a-4a62-87e1-2e9c23d16949
-- title:
--   Theorem 2.4: global uniqueness for phaseless inverse scattering in dimension one
-- statement:
--   Let $v$ and $w$ be real-valued potentials in $L^1_1(\mathbb R)$ vanishing on $(-\infty,0)$, with scattering data $\psi_v^+(x,k)$, $s_{21,v}(k)$ and $\psi_w^+(x,k)$, $s_{21,w}(k)$ for all $k>0$ as in (1.4). Then:
--
--   1. if $x_1,x_2<0$, $x_1\ne x_2$, and $S_1(x_1,x_2,k)$ coincide for $v$ and $w$ for every $k>0$, i.e. $|s_{21,v}(k)|^2=|s_{21,w}(k)|^2$ and $|\psi_v^+(x_i,k)|^2=|\psi_w^+(x_i,k)|^2$ for $i=1,2$, then $v=w$ almost everywhere;
--   2. if $x_1,x_2,x_3<0$ are pairwise distinct and $|\psi_v^+(x_i,k)|^2=|\psi_w^+(x_i,k)|^2$ for $i=1,2,3$ and every $k>0$, then $v=w$ almost everywhere;
--   3. if $x<0$ and $|\psi_v^+(x,k)|^2=|\psi_w^+(x,k)|^2$ and $\frac{d}{dx}|\psi_v^+(x,k)|^2=\frac{d}{dx}|\psi_w^+(x,k)|^2$ for every $k>0$, then $v=w$ almost everywhere.
--
--   That is, each of the phaseless data $S_1(x_1,x_2,\cdot)$, $S_2(x_1,x_2,x_3,\cdot)$, $S_3(x,\cdot)$ on $\mathbb R_+$ uniquely determines $v$ on $\mathbb R$. This is global uniqueness for phaseless inverse scattering on the line for potentials supported on a half-line.
--
--   **Formalization Note** "Uniquely determine" is stated as: two admissible potentials with the same data are equal almost everywhere, which is equality in $L^1_1(\mathbb R)$. The reconstruction procedure mentioned in the paper ("via formulas ... and results of [NM]") is not part of the formal statement. The data are required for all $k>0$, as in the paper; the points $x_i$ are only required to be distinct, as in (1.10)-(1.11).
-- source:
--   R. G. Novikov, Phaseless inverse scattering in the one-dimensional case, arXiv:1503.02159v1 (2015), claim c005; Section 2, Theorem 2.4, PDF p. 4 (data: eqs. (1.10)-(1.12), PDF p. 3)

import Mathlib
import Definitions.Def_Arxiv1503_02159_Basic

open MeasureTheory Filter Topology

namespace Arxiv1503_02159

theorem phaseless_global_uniqueness (v w : ℝ → ℝ)
    (hv : IsAdmissiblePotential v) (hw : IsAdmissiblePotential w)
    (ψv ψw : ℝ → ℝ → ℂ) (s21v s22v s21w s22w : ℝ → ℂ)
    (hψv : IsScatteringData v ψv s21v s22v) (hψw : IsScatteringData w ψw s21w s22w) :
    (∀ x1 x2 : ℝ, x1 < 0 → x2 < 0 → x1 ≠ x2 →
      (∀ k : ℝ, 0 < k → dataS1 ψv s21v x1 x2 k = dataS1 ψw s21w x1 x2 k) →
      v =ᵐ[volume] w) ∧
    (∀ x1 x2 x3 : ℝ, x1 < 0 → x2 < 0 → x3 < 0 → x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 →
      (∀ k : ℝ, 0 < k → dataS2 ψv x1 x2 x3 k = dataS2 ψw x1 x2 x3 k) →
      v =ᵐ[volume] w) ∧
    (∀ x : ℝ, x < 0 →
      (∀ k : ℝ, 0 < k → dataS3 ψv x k = dataS3 ψw x k) →
      v =ᵐ[volume] w) := by sorry

end Arxiv1503_02159
