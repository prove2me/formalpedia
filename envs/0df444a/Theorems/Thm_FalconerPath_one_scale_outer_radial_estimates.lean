-- Prove2me | Theorems.Thm_FalconerPath_one_scale_outer_radial_estimates
-- name    : FalconerPath.one_scale_outer_radial_estimates
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:29.582206+00:00
-- url     : https://prove2.me/theorems/32e90043-cc5c-4538-9640-610aa5d56e1e
-- title:
--   Outer-interval radial fiber estimates
-- statement:
--   Let $k\ge2$ and let $s,q,\zeta,L,a,C$ be real parameters. Take a sequence of normalized regular-class data with these fixed parameters, with $N_j\to\infty$ and $h_j\to0$, whose profiles converge uniformly on $[0,1]$ to a function $m$. Suppose $0<A<B<1$, $m(w)\ge qw$ for $w\in[0,A]$, and $m(w)-m(B)\ge q(w-B)$ for $w\in[B,1]$. Let $e,W>0$.
--
--   For all sufficiently large $j$ there is a Borel $H_j\subset G_j$ with deleted product mass at most $R_j^{-e/2}$. Put $a_0=0$, $a_1=\lfloor AN_j\rfloor$, $a_2=\lfloor BN_j\rfloor$, and $a_3=N_j$. For every $i<3$, every $(x,z)\in H_j$, and every depth-$a_i$ cell $Q$ containing $z$,
--
--   $$\rho_j\{z^\prime\in Q:|\pi_x(z^\prime)-\pi_x(z)|\le W2^{-a_{i+1}}\}\le f_i\rho_j(Q),$$
--
--   where $f_0=R_j^{-qA+e}$, $f_1=1$, and $f_2=R_j^{-q(1-B)+e}$.
--
--   Here a normalized regular-class datum consists of an integer $N_j$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$ with supports in $\overline B(0,L)$ and cross distances at least $a$, a translated half-open unit root carrying $\rho_j$, a nonnegative error $h_j$, and a profile $m_j$ with $m_j(0)=0$, nondecreasing and $(k+1)$-Lipschitz on $[0,1]$, satisfying $m_j(u)\ge su-h_j$. In its translated dyadic grid, every occupied depth-$b$ cell has $\rho_j$-mass between $R_j^{-m_j(b/N_j)-h_j}$ and $R_j^{-m_j(b/N_j)+h_j}$, for $b\le N_j$, where $R_j=2^{N_j}$. For occupied nested cells $P\subset Q$ at depths $c\ge b$, $c\le N_j$, the ratio $\rho_j(P)/\rho_j(Q)$ lies between $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]-h_j}$ and $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]+h_j}$. The datum includes a Borel $G_j\subset\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$ such that, for $\rho_j$-almost every $z$, the unnormalized reverse law $(\pi_z)_\#(\nu_j|_{G_j^z})$ obeys cap bounds $R_j^{h_j}u^q$ and directional plate bounds $\max(Cu^\zeta,0)$ for $R_j^{-1}\le u\le1$. The geometry constants $L,a$ are positive. The Lean statement packages the two outer tests on one retained relation, with the unrestricted full conditional source law and the trivial middle factor.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, proof paragraph beginning “First consider [0,A] or [B,1]”, equations labeled prep:local-ball and prep:local-mean, and the following paragraph beginning “Fubini and Markov therefore delete only”.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem one_scale_outer_radial_estimates {k : ℕ} (hk : 2 ≤ k)
    (s q ζ L a C : ℝ) (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (herr : Tendsto (fun j => (X j).err) atTop (𝓝 0))
    (m : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
      |(X j).m u-m u| < ε)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1)
    (hfirst : ∀ w ∈ Icc 0 A, q*w ≤ m w)
    (hlast : ∀ w ∈ Icc B 1, q*(w-B) ≤ m w-m B)
    (e W : ℝ) (he : 0 < e) (hW : 0 < W) :
    ∀ᶠ j in atTop, ∃ H : PairSet (k+1), MeasurableSet H ∧ H ⊆ (X j).G ∧
      ((X j).ν.prod (X j).ρ) ((X j).G \ H) ≤
        ENNReal.ofReal ((scale (X j).N)^(-e/2)) ∧
      LocalFiberBounds false (X j).ρ H (fun _ => univ) (X j).v
        (contactDepths (X j).N A B) 3
        (fun i => if i = 0 then (scale (X j).N)^(-q*A+e)
          else if i = 2 then (scale (X j).N)^(-q*(1-B)+e) else 1) W := by sorry
end FalconerPath
