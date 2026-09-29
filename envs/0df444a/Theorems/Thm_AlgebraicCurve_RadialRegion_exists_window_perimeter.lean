-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter
-- name    : AlgebraicCurve.RadialRegion.exists_window_perimeter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/9dacc11a-523f-5881-b2f3-a277ff0ec628
-- title:
--   Grid window as a radial region with perimeter arcs
-- statement:
--   Let $o,h$ be real numbers with $h>0$ (written `hm` in the statement), let $j_{\mathrm{lo}}\le j_{\mathrm{hi}}$ and $k_{\mathrm{lo}}\le k_{\mathrm{hi}}$ be integers, and let $cy:\mathbb Z\times\mathbb Z\to\mathbb R$ assign to each pair $(j,k)$ a height strictly inside the $k$-th horizontal strip, $o+kh<cy(j,k)<o+(k+1)h$. Assume the origin is interior to the window, $o+j_{\mathrm{lo}}h<0<o+(j_{\mathrm{hi}}+1)h$ and $o+k_{\mathrm{lo}}h<0<o+(k_{\mathrm{hi}}+1)h$, and that $cy(j_{\mathrm{hi}},k)=0$ for every integer $k$ whose strip contains $0$. Then there is a `RadialRegion` $R$ — a centre $q$, a continuous, $2\pi$-periodic, strictly positive radius $r:\mathbb R\to\mathbb R$, and a strictly increasing subdivision $0=\varphi_0<\dots<\varphi_N=2\pi$ with $r$ twice continuously differentiable on each $\mathrm{arcIcc}\,k=[\varphi_k,\varphi_{k+1}]$ — such that: $q=0$; $R.K$ is the closed rectangle $[o+j_{\mathrm{lo}}h,\,o+(j_{\mathrm{hi}}+1)h]\times[o+k_{\mathrm{lo}}h,\,o+(k_{\mathrm{hi}}+1)h]$ and $R.\mathrm{Kint}=\{z:\lVert z-q\rVert<r(\arg(z-q))\}$ is the corresponding open rectangle; $N=2(j_{\mathrm{hi}}-j_{\mathrm{lo}}+1)+4(k_{\mathrm{hi}}-k_{\mathrm{lo}}+1)$; the map $k\mapsto \mathrm{arcSet}\,k=\mathrm{loop}([\varphi_k,\varphi_{k+1}])$, where $\mathrm{loop}(\varphi)=q+r(\varphi)e^{i\varphi}$, is injective; and every arc is of exactly one of six shapes, each coming with its two endpoints $\mathrm{loop}(\varphi_k)$, $\mathrm{loop}(\varphi_{k+1})$, a formula for $r$ on $[\varphi_k,\varphi_{k+1}]$ and a confinement of that interval: for some column $j_{\mathrm{lo}}\le j\le j_{\mathrm{hi}}$, the bottom side $\{\operatorname{im}z=o+k_{\mathrm{lo}}h,\ \operatorname{re}z\in[o+jh,o+(j+1)h]\}$ traversed left to right with $r(t)=\bigl(-\sin t/(-(o+k_{\mathrm{lo}}h))\bigr)^{-1}$ and $[\varphi_k,\varphi_{k+1}]\subseteq(\pi,2\pi)$, or the top side $\{\operatorname{im}z=o+(k_{\mathrm{hi}}+1)h,\ \operatorname{re}z\in[o+jh,o+(j+1)h]\}$ traversed right to left with $r(t)=\bigl(\sin t/(o+(k_{\mathrm{hi}}+1)h)\bigr)^{-1}$ and $[\varphi_k,\varphi_{k+1}]\subseteq(0,\pi)$; or, for some row $k_{\mathrm{lo}}\le k_0\le k_{\mathrm{hi}}$, one of the two pieces into which the height $cy(j_{\mathrm{lo}},k_0)$ cuts the left side $\{\operatorname{re}z=o+j_{\mathrm{lo}}h\}$ over that row, traversed downwards, with $r(t)=\bigl(-\cos t/(-(o+j_{\mathrm{lo}}h))\bigr)^{-1}$ and $[\varphi_k,\varphi_{k+1}]\subseteq(\pi/2,3\pi/2)$, or one of the two pieces into which $cy(j_{\mathrm{hi}},k_0)$ cuts the right side $\{\operatorname{re}z=o+(j_{\mathrm{hi}}+1)h\}$ over that row, traversed upwards, with $r(t)=\bigl(\cos t/(o+(j_{\mathrm{hi}}+1)h)\bigr)^{-1}$ and $[\varphi_k,\varphi_{k+1}]$ contained in $(-\pi/2,\pi/2)$ or in $(3\pi/2,5\pi/2)$. Six further clauses state the converse: each of these six families of segments, for every admissible $j$ resp. $k_0$, is realised as $\mathrm{arcSet}\,k$ for some $k$.
--
--   This is the geometric input for the cell dissection: a rectangular window of a square grid, with the origin in its interior, is exhibited as a star-shaped (radial) region about the origin whose boundary subdivision consists precisely of the sides of the grid squares along the bottom and top rows and the two pieces, cut by a prescribed interior height, of the outer sides of the squares in the left and right columns. It is used by [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily), and is obtained from the six-arc description of a single rectangle together with the exact refinement of a radial subdivision.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_window_perimeter.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_window_perimeter (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hj : jlo ≤ jhi) (hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ)
    (hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm)
    (hx₀ : o + jlo * hm < 0) (hx₁ : 0 < o + (jhi + 1) * hm)
    (hy₀ : o + klo * hm < 0) (hy₁ : 0 < o + (khi + 1) * hm)
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0) :
    ∃ R : RadialRegion,
      R.q = 0 ∧
      R.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      R.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') ∧
      (∀ k : Fin R.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          R.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))} ∧
          R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)} ∧
          R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
          R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
        R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)}) := by sorry
