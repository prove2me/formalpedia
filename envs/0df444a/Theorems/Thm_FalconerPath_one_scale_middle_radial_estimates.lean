-- Prove2me | Theorems.Thm_FalconerPath_one_scale_middle_radial_estimates
-- name    : FalconerPath.one_scale_middle_radial_estimates
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-03T20:20:36.913982+00:00
-- url     : https://prove2.me/theorems/7b48cfbf-1899-4d1f-8d2e-2a5092a3fbc6
-- title:
--   Middle-interval radial gain from bad-direction exclusion
-- statement:
--   Fix $k\ge2$, $k-1\le q<k-\tfrac12$, $k-\tfrac12<t<k$, and $\zeta,L,a,C>0$, with $s$ any real parameter. Take a sequence of normalized regular-class data for these parameters, with $N_j\to\infty$, $h_j\to0$, and profiles converging uniformly on $[0,1]$ to $m$. Suppose $0<A<B<1$, $B<2A$, and $m(w)-m(A)\ge t(w-A)$ for every $w\in[A,B]$. Let $W>0$.
--
--   There is $c_1>0$ such that for all sufficiently large $j$ there is a Borel $H_j\subset G_j$ deleting product mass at most $R_j^{-c_1(B-A)/2}$. At the four depths $a_0=0$, $a_1=\lfloor AN_j\rfloor$, $a_2=\lfloor BN_j\rfloor$, $a_3=N_j$, for every $i<3$, every retained witness $(x,z)$, and every depth-$a_i$ cell $Q$ containing $z$,
--
--   $$\rho_j\{z^\prime\in Q:|\pi_x(z^\prime)-\pi_x(z)|\le W2^{-a_{i+1}}\}\le f_i\rho_j(Q),$$
--
--   where $f_1=R_j^{-(q+c_1/2)(B-A)}$ and $f_0=f_2=1$.
--
--   Here a normalized regular-class datum consists of an integer $N_j$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$ with supports in $\overline B(0,L)$ and cross distances at least $a$, a translated half-open unit root carrying $\rho_j$, a nonnegative error $h_j$, and a profile $m_j$ with $m_j(0)=0$, nondecreasing and $(k+1)$-Lipschitz on $[0,1]$, satisfying $m_j(u)\ge su-h_j$. In its translated dyadic grid, every occupied depth-$b$ cell has $\rho_j$-mass between $R_j^{-m_j(b/N_j)-h_j}$ and $R_j^{-m_j(b/N_j)+h_j}$, for $b\le N_j$, where $R_j=2^{N_j}$. For occupied nested cells $P\subset Q$ at depths $c\ge b$, $c\le N_j$, the ratio $\rho_j(P)/\rho_j(Q)$ lies between $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]-h_j}$ and $R_j^{-[m_j(c/N_j)-m_j(b/N_j)]+h_j}$. The datum includes a Borel $G_j\subset\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$ such that, for $\rho_j$-almost every $z$, the unnormalized reverse law $(\pi_z)_\#(\nu_j|_{G_j^z})$ obeys cap bounds $R_j^{h_j}u^q$ and directional plate bounds $\max(Cu^\zeta,0)$ for $R_j^{-1}\le u\le1$. The geometry constants $L,a$ are positive. The Lean statement isolates the proof's Borel middle-interval deletion and bounds the full conditional source law at each retained witness.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf. Section 5.1, Lemma 5.3 (One-scale improvement), label prep:one-scale, proof from “For the middle interval put D=” through “Every remaining witness satisfies”, including the angular envelope deletion, equation prep:witness-bad, witness-to-center comparison, equation prep:linearization-margin, Taylor expansion, and heavy-cell cover.

import Definitions.Def_FalconerPath_defs
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
theorem one_scale_middle_radial_estimates {k : ℕ} (hk : 2 ≤ k)
    (s q ζ L a C t : ℝ) (hq : (k:ℝ)-1 ≤ q) (hqS : q < (k:ℝ)-1/2)
    (ht : (k:ℝ)-1/2 < t) (htk : t < k) (hζ : 0 < ζ)
    (hL : 0 < L) (ha : 0 < a) (hC : 0 < C)
    (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (herr : Tendsto (fun j => (X j).err) atTop (𝓝 0))
    (m : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
      |(X j).m u-m u| < ε)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1) (hBA : B < 2*A)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A)
    (W : ℝ) (hW : 0 < W) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ j in atTop,
      ∃ H : PairSet (k+1), MeasurableSet H ∧ H ⊆ (X j).G ∧
        ((X j).ν.prod (X j).ρ) ((X j).G \ H) ≤
          ENNReal.ofReal ((scale (X j).N)^(-c₁*(B-A)/2)) ∧
        LocalFiberBounds false (X j).ρ H (fun _ => univ) (X j).v
          (contactDepths (X j).N A B) 3
          (fun i => if i = 1 then (scale (X j).N)^(-(q+c₁/2)*(B-A)) else 1) W := by sorry
end FalconerPath
