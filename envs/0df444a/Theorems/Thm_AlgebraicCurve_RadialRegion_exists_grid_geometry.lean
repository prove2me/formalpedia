-- Prove2me | Theorems.Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry
-- name    : AlgebraicCurve.RadialRegion.exists_grid_geometry
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/cf9d63d8-0d2e-5a36-86be-b1e345467c5d
-- title:
--   Pairing, reparametrisation and vertex data for a square grid
-- statement:
--   Throughout, a *radial region* is a structure $R$ consisting of a centre $R.q \in \mathbb{C}$, a continuous, $2\pi$-periodic, everywhere positive radius function $R.r : \mathbb{R} \to \mathbb{R}$, a number $R.N$ of arcs, and breakpoints $R.\varphi s : \mathrm{Fin}(R.N+1) \to \mathbb{R}$ with $R.\varphi s(0)=0$, $R.\varphi s(\mathrm{last})=2\pi$, strictly increasing, such that $R.r$ is $C^2$ on each $[R.\varphi s(i^{\flat}), R.\varphi s(i^{\sharp})]$ (here $i^{\flat}=i.\mathrm{castSucc}$, $i^{\sharp}=i.\mathrm{succ}$). One writes `loop` for $\varphi \mapsto R.q + R.r(\varphi)e^{i\varphi}$, `arcIcc k` for the parameter interval $[R.\varphi s(k^{\flat}), R.\varphi s(k^{\sharp})]$, `arcSet k` for its image under `loop`, and `Kint` for the star-shaped open set $\{z : \lVert z-R.q\rVert < R.r(\arg(z-R.q))\}$; `K` denotes the further set attached to a radial region by the same structure.
--
--   The data of the theorem are: real numbers $o$ (origin) and `hm` with $0 <$ `hm` (mesh); integers $jlo, jhi, klo, khi$ with $jlo+1<jhi$ and $klo+1<khi$ (the window is at least three cells wide and high); and a map $ctr : \mathbb{Z}\times\mathbb{Z}\to\mathbb{C}$. Write $x_j := o + j\cdot$ `hm` and $y_k := o + k\cdot$ `hm`, so that the cell indexed by $p=(p_1,p_2)$ is $[x_{p_1},x_{p_1+1}]\times[y_{p_2},y_{p_2+1}]$ and the window is $[x_{jlo},x_{jhi+1}]\times[y_{klo},y_{khi+1}]$.
--
--   Hypotheses on these data: `hctr` requires $\mathrm{Re}\,ctr(p)$ to lie in the open interval $(x_{p_1},x_{p_1+1})$ and $\mathrm{Im}\,ctr(p)$ in $(y_{p_2},y_{p_2+1})$ for every $p$, i.e. every cell centre is interior to its cell; `hzero` requires $x_{jlo}<0<x_{jhi+1}$ and $y_{klo}<0<y_{khi+1}$, i.e. the origin of $\mathbb{C}$ is interior to the window in both coordinates; `hcy0` requires that for every integer $k$ with $y_k<0<y_{k+1}$ the centre $ctr(jhi,k)$ has vanishing imaginary part.
--
--   A family of radial regions $base : \mathbb{Z}\times\mathbb{Z}\to$ `RadialRegion` is given, subject to the conjunction `hbase`, which for every $p$ asserts: $(base\,p).q = ctr(p)$ and $(base\,p).N = 6$; $(base\,p).K$ is the closed cell $[x_{p_1},x_{p_1+1}]\times[y_{p_2},y_{p_2+1}]$ and $(base\,p).Kint$ the corresponding open cell. Writing $\mu_p := \mathrm{Im}\,ctr(p)$ if $p_1 = jlo$ and $\mu_p := \mathrm{Im}\,ctr(p_1-1,p_2)$ otherwise (the splitting height of the left side, dictated by the left neighbour's centre), the six arc sets are prescribed as: $k=0$, the upper part $\{\mathrm{Re}=x_{p_1+1},\ \mathrm{Im}\in[\mathrm{Im}\,ctr(p),\,y_{p_2+1}]\}$ of the right side; $k=1$, the top side $\{\mathrm{Im}=y_{p_2+1},\ \mathrm{Re}\in[x_{p_1},x_{p_1+1}]\}$; $k=2$, $\{\mathrm{Re}=x_{p_1},\ \mathrm{Im}\in[\mu_p,\,y_{p_2+1}]\}$; $k=3$, $\{\mathrm{Re}=x_{p_1},\ \mathrm{Im}\in[y_{p_2},\,\mu_p]\}$; $k=4$, the bottom side $\{\mathrm{Im}=y_{p_2},\ \mathrm{Re}\in[x_{p_1},x_{p_1+1}]\}$; $k=5$, $\{\mathrm{Re}=x_{p_1+1},\ \mathrm{Im}\in[y_{p_2},\,\mathrm{Im}\,ctr(p)]\}$. The seven breakpoint values of `loop` are prescribed in the same order: $(x_{p_1+1},\mathrm{Im}\,ctr(p))$, $(x_{p_1+1},y_{p_2+1})$, $(x_{p_1},y_{p_2+1})$, $(x_{p_1},\mu_p)$, $(x_{p_1},y_{p_2})$, $(x_{p_1+1},y_{p_2})$ and again $(x_{p_1+1},\mathrm{Im}\,ctr(p))$ at the index $6$. The radius is prescribed on each arc by the line supporting it: $r(t) = (\cos t/(x_{p_1+1}-\mathrm{Re}\,ctr(p)))^{-1}$ on the arcs $0$ and $5$, $r(t) = (\sin t/(y_{p_2+1}-\mathrm{Im}\,ctr(p)))^{-1}$ on the arc $1$, $r(t) = (-\cos t/(\mathrm{Re}\,ctr(p)-x_{p_1}))^{-1}$ on the arcs $2$ and $3$, and $r(t) = (-\sin t/(\mathrm{Im}\,ctr(p)-y_{p_2}))^{-1}$ on the arc $4$. The parameter intervals are confined as follows: arc $0$ inside $[0,\pi/2)$, arc $1$ inside $(0,\pi)$, arcs $2$ and $3$ inside $(\pi/2,3\pi/2)$, arc $4$ inside $(\pi,2\pi)$, arc $5$ inside $(3\pi/2,2\pi]$. Finally `hbase` requires that for $z\in (base\,p).K\setminus (base\,p).Kint$ one has $(base\,p).\mathrm{loop}(\theta)=z$, where $\theta$ is $\arg(z-ctr(p))$ shifted by $2\pi$ when negative, and that for $t_1\le t_2$ in one and the same `arcIcc k` the image $(base\,p).\mathrm{loop}\,''[t_1,t_2]$ is the real segment joining $(base\,p).\mathrm{loop}(t_1)$ to $(base\,p).\mathrm{loop}(t_2)$ — the arcs are straight.
--
--   A further radial region $winReg$ is given, subject to the conjunction `hwin`: $winReg.q = 0$; $winReg.K$ is the closed window and $winReg.Kint$ the open window; $winReg.N = 2(jhi-jlo+1)_{\mathbb{N}} + 4(khi-klo+1)_{\mathbb{N}}$; the map $k\mapsto winReg.\mathrm{arcSet}\,k$ is injective; every arc of $winReg$ falls into one of six types, namely (with $jlo\le j\le jhi$ resp. $klo\le k_0\le khi$): a bottom edge $\{\mathrm{Im}=y_{klo},\ \mathrm{Re}\in[x_j,x_{j+1}]\}$ traversed from $(x_j,y_{klo})$ to $(x_{j+1},y_{klo})$ with $r(t)=(-\sin t/(-y_{klo}))^{-1}$ and parameters in $(\pi,2\pi)$; a top edge $\{\mathrm{Im}=y_{khi+1},\ \mathrm{Re}\in[x_j,x_{j+1}]\}$ traversed from $(x_{j+1},y_{khi+1})$ to $(x_j,y_{khi+1})$ with $r(t)=(\sin t/y_{khi+1})^{-1}$ and parameters in $(0,\pi)$; the upper left piece $\{\mathrm{Re}=x_{jlo},\ \mathrm{Im}\in[\mathrm{Im}\,ctr(jlo,k_0),\,y_{k_0+1}]\}$ traversed downwards from $(x_{jlo},y_{k_0+1})$ to $(x_{jlo},\mathrm{Im}\,ctr(jlo,k_0))$, and the lower left piece $\{\mathrm{Re}=x_{jlo},\ \mathrm{Im}\in[y_{k_0},\mathrm{Im}\,ctr(jlo,k_0)]\}$ traversed downwards to $(x_{jlo},y_{k_0})$, both with $r(t)=(-\cos t/(-x_{jlo}))^{-1}$ and parameters in $(\pi/2,3\pi/2)$; the lower right piece $\{\mathrm{Re}=x_{jhi+1},\ \mathrm{Im}\in[y_{k_0},\mathrm{Im}\,ctr(jhi,k_0)]\}$ traversed upwards from $(x_{jhi+1},y_{k_0})$, and the upper right piece $\{\mathrm{Re}=x_{jhi+1},\ \mathrm{Im}\in[\mathrm{Im}\,ctr(jhi,k_0),\,y_{k_0+1}]\}$ traversed upwards to $(x_{jhi+1},y_{k_0+1})$, both with $r(t)=(\cos t/x_{jhi+1})^{-1}$ and parameters in $(-\pi/2,\pi/2)$ or else in $(3\pi/2,5\pi/2)$; and, conversely, six clauses asserting that each of these six families of segments is realised: for every $j\in[jlo,jhi]$ the bottom and the top edge over $[x_j,x_{j+1}]$ occur as arc sets of $winReg$, and for every $k_0\in[klo,khi]$ the four pieces of the left and right sides listed above occur as arc sets of $winReg$.
--
--   Under these hypotheses there exist orientation bits $sqbit : \forall p,\ \mathrm{Fin}\,(base\,p).N \to \mathrm{Bool}$ and $perbit : \mathrm{Fin}\,winReg.N \to \mathrm{Bool}$, a finite set $B_0 \subseteq \mathbb{C}$, and predicates $Shares,\ Contains$ on $\mathrm{Option}(\mathbb{Z}\times\mathbb{Z})$ (a window cell, or `none` for the exterior region) applied to sets of complex numbers, resp. to complex numbers, such that all of the following hold.
--
--   (1) For each $p$, the map $k\mapsto (base\,p).\mathrm{arcSet}\,k$ on $\mathrm{Fin}\,(base\,p).N$ is injective. (2) For $p \ne p'$ and arcs $k$ of $base\,p$, $k'$ of $base\,p'$ with the same arc set, $sqbit\,p'\,k' = \neg\, sqbit\,p\,k$. (3) For $p$ in the window $[jlo,jhi]\times[klo,khi]$ and an arc $k$ of $base\,p$ whose arc set equals that of an arc $k_0$ of $winReg$, $perbit\,k_0 = \neg\, sqbit\,p\,k$.
--
--   (4) For $p\ne p'$ and arcs $k$, $k'$ with the same arc set and $sqbit\,p\,k = \mathrm{true}$, there is $\psi:\mathbb{R}\to\mathbb{R}$, strictly decreasing and $C^1$ on $(base\,p').\mathrm{arcIcc}\,k'$, carrying the initial breakpoint of $k'$ to the terminal breakpoint of $k$ and the terminal one to the initial one, with $(base\,p').\mathrm{loop}\,t = (base\,p).\mathrm{loop}(\psi t)$ on $(base\,p').\mathrm{arcIcc}\,k'$. (5) For $p$ in the window and an arc $k$ of $base\,p$ with the same arc set as an arc $k_0$ of $winReg$ and $sqbit\,p\,k=\mathrm{true}$, there is $\psi$, strictly increasing and $C^1$ on $winReg.\mathrm{arcIcc}\,k_0$, matching the initial and terminal breakpoints of $k_0$ with those of $k$, such that $winReg.\mathrm{loop}\,t = (base\,p).\mathrm{loop}(\psi t)$ there. (6) In the same situation but with $sqbit\,p\,k = \mathrm{false}$, there is $\psi$, strictly increasing and $C^1$ on $(base\,p).\mathrm{arcIcc}\,k$, matching breakpoints in the other direction, with $(base\,p).\mathrm{loop}\,t = winReg.\mathrm{loop}(\psi t)$ there.
--
--   (7) $Shares\,(\mathrm{some}\ p)\,Z$ holds if and only if $p$ lies in the window and $Z$ is one of the arc sets of $base\,p$. (8) $Shares\,\mathrm{none}\,Z$ holds if and only if $Z$ is an arc set of $winReg$. (9) $Contains\,(\mathrm{some}\ p)\,v$ holds if and only if $p$ lies in the window and $v \in (base\,p).K$. (10) $Contains\,\mathrm{none}\,v$ holds if and only if $v \notin winReg.Kint$.
--
--   (11) For every $\rho$ and $Z$ with $Shares\,\rho\,Z$ there is $\rho' \ne \rho$ with $Shares\,\rho'\,Z$ such that any $\rho''$ with $Shares\,\rho''\,Z$ equals $\rho$ or $\rho'$: each segment is shared by exactly two regions. (12) For every $v$ and all $\rho,\rho'$ with $Contains\,\rho\,v$ and $Contains\,\rho'\,v$, the pair $(\rho,\rho')$ lies in the reflexive–transitive closure of the relation «$\rho_1$ and $\rho_2$ share some $Z$ with $v\in Z$».
--
--   (13) $\#B_0 = ((jhi-jlo+1)_{\mathbb{N}}+1)\,((khi-klo+1)_{\mathbb{N}}+1) + (jhi-jlo+1)_{\mathbb{N}}(khi-klo+1)_{\mathbb{N}} + (khi-klo+1)_{\mathbb{N}}$. (14) For every $p$ in the window and every $i \in \mathrm{Fin}((base\,p).N+1)$, the breakpoint value $(base\,p).\mathrm{loop}((base\,p).\varphi s\,i)$ lies in $B_0$. (15) Likewise every $winReg.\mathrm{loop}(winReg.\varphi s\,i)$ lies in $B_0$. (16) Every $v\in B_0$ is an endpoint value $(base\,p).\mathrm{loop}((base\,p).\varphi s\,k^{\flat})$ or $(base\,p).\mathrm{loop}((base\,p).\varphi s\,k^{\sharp})$ of some arc $k$ of some cell $p$ in the window. (17) Every $v \in B_0$ satisfies $\mathrm{Re}\,v - o = j\cdot$ `hm` for some integer $j$.
--
--   This is the planar bookkeeping behind a cell dissection by radial regions: a window of grid squares, each presented as a six-arc radial region about an interior centre, together with the radial region presenting the window's perimeter about the origin, is equipped with orientation bits on arcs, $C^1$ reparametrisations identifying the two presentations of each shared segment, the two-regions-per-segment and vertex-connectivity properties, and an explicit finite set of breakpoints. It is used by [`AlgebraicCurve.exists_pairedCellFamily`](thm.html#AlgebraicCurve.exists_pairedCellFamily), and the reparametrisations are produced from [`AlgebraicCurve.RadialRegion.exists_reparam_across_edge`](thm.html#AlgebraicCurve.RadialRegion.exists_reparam_across_edge) and [`AlgebraicCurve.RadialRegion.exists_reparam_same_side`](thm.html#AlgebraicCurve.RadialRegion.exists_reparam_same_side).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RadialRegion_exists_grid_geometry.lean

import Definitions.Def_AlgebraicCurve_CellDissection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real
open AlgebraicCurve Set

theorem AlgebraicCurve.RadialRegion.exists_grid_geometry (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hjlt : jlo + 1 < jhi) (hklt : klo + 1 < khi) (ctr : ℤ × ℤ → ℂ)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
      0 < o + (khi + 1) * hm))
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0)
    (base : ℤ × ℤ → RadialRegion)
    (hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂)))
    (winReg : RadialRegion)
    (hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})) :
    ∃ (sqbit : ∀ p : ℤ × ℤ, Fin (base p).N → Bool) (perbit : Fin winReg.N → Bool) (B₀ : Finset ℂ)
      (Shares : Option (ℤ × ℤ) → Set ℂ → Prop) (Contains : Option (ℤ × ℤ) → ℂ → Prop),
      (∀ (p : ℤ × ℤ) (k k' : Fin (base p).N), (base p).arcSet k = (base p).arcSet k' → k = k') ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p' k' = !sqbit p k) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ →
          perbit k₀ = !sqbit p k) ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((base p').arcIcc k') ∧
          ψ ((base p').φs k'.castSucc) = (base p).φs k.succ ∧
          ψ ((base p').φs k'.succ) = (base p).φs k.castSucc ∧
          ∀ t ∈ (base p').arcIcc k', (base p').loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (winReg.arcIcc k₀) ∧
          ψ (winReg.φs k₀.castSucc) = (base p).φs k.castSucc ∧
          ψ (winReg.φs k₀.succ) = (base p).φs k.succ ∧
          ∀ t ∈ winReg.arcIcc k₀, winReg.loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = false →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((base p).arcIcc k) ∧
          ψ ((base p).φs k.castSucc) = winReg.φs k₀.castSucc ∧
          ψ ((base p).φs k.succ) = winReg.φs k₀.succ ∧
          ∀ t ∈ (base p).arcIcc k, (base p).loop t = winReg.loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (Z : Set ℂ), Shares (some p) Z ↔
        p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧ ∃ k : Fin (base p).N, (base p).arcSet k = Z) ∧
      (∀ Z : Set ℂ, Shares none Z ↔ ∃ k₀ : Fin winReg.N, winReg.arcSet k₀ = Z) ∧
      (∀ (p : ℤ × ℤ) (v : ℂ), Contains (some p) v ↔ p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧
        v ∈ (base p).K) ∧
      (∀ v : ℂ, Contains none v ↔ v ∉ winReg.Kint) ∧
      (∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares ρ Z →
        ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares ρ' Z ∧
          ∀ ρ'' : Option (ℤ × ℤ), Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ') ∧
      (∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains ρ v → Contains ρ' v →
        Relation.ReflTransGen
          (fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Shares ρ₁ Z ∧ Shares ρ₂ Z ∧ v ∈ Z) ρ ρ') ∧
      B₀.card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat ∧
      (∀ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∀ i : Fin ((base p).N + 1), (base p).loop
        ((base p).φs i) ∈ B₀) ∧
      (∀ i : Fin (winReg.N + 1), winReg.loop (winReg.φs i) ∈ B₀) ∧
      (∀ v ∈ B₀, ∃ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∃ k : Fin (base p).N,
        v = (base p).loop ((base p).φs k.castSucc) ∨ v = (base p).loop ((base p).φs k.succ)) ∧
      (∀ v ∈ B₀, ∃ j : ℤ, v.re - o = j * hm) := by sorry
