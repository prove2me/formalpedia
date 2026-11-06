-- Prove2me | Theorems.Thm_FalconerPath_middle_scale_preparation
-- name    : FalconerPath.middle_scale_preparation
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:15:04.15189+00:00
-- url     : https://prove2.me/theorems/57040622-0d8c-4fb1-818c-5eaa95e4174a
-- title:
--   Conditional source and reverse direction bounds at the middle scale
-- statement:
--   Let $k\in\mathbb N$ and $s,q,\zeta,L,a,C\in\mathbb R$. For every $j\in\mathbb N$, let $X_j$ consist of $N_j\in\mathbb N$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$, a translation $v_j$, a real function $m_j$, an error $e_j\ge0$, and a Borel relation $G_j$. Assume $L,a>0$, both supports lie in $\overline B(0,L)$, and $\|x-z\|\ge a$ for every $x\in\operatorname{supp}\nu_j$ and $z\in\operatorname{supp}\rho_j$. The measure $\rho_j$ is carried by the half-open unit grid cell $Q(v_j,0,0)$. On $[0,1]$, $m_j$ is nondecreasing and $(k+1)$-Lipschitz, $m_j(0)=0$, and $m_j(u)\ge su-e_j$. Put $R_j=2^{N_j}$. For every $\ell\le N_j$ and cell $Q=Q(v_j,\ell,i)$ with positive mass, require $R_j^{-m_j(\ell/N_j)-e_j}\le\rho_j(Q)\le R_j^{-m_j(\ell/N_j)+e_j}$. For every $0\le\ell\le h\le N_j$ and nested cells $Q'=Q(v_j,h,i')\subseteq Q=Q(v_j,\ell,i)$ with $\rho_j(Q')>0$, require $R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))-e_j}\le\rho_j(Q')/\rho_j(Q)\le R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))+e_j}$. At $N_j=0$ real division uses $0/0=0$. Assume $G_j\subseteq\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$. Define $\lambda_{j,z}=(\pi_z)_\#(\nu_j|_{\{x:(x,z)\in G_j\}})$, where $\pi_z(x)=\|x-z\|^{-1}(x-z)$ with value zero at $x=z$. For $\rho_j$-almost every $z$, every $w\in S^k$ and every $2^{-N_j}\le u\le1$ with $u>0$ satisfy $\lambda_{j,z}(B(w,u))\le R_j^{e_j}u^q$. Also, for $\rho_j$-almost every $z$, every $v\in S^k$ and the same radii satisfy $\lambda_{j,z}\{w\in S^k:|\langle w,v\rangle|\le u\}\le[Cu^\zeta]_+$. Here $[u]_+=\max(u,0)$ in the extended nonnegative reals. These are the conditions encoded by $X_j\in\mathrm{RadialClassData}(k,s,q,\zeta,L,a,C)$. Assume $N_j\to\infty$. Let $t\in\mathbb R$. Assume $e_j\to0$ and $m_j\to m$ uniformly on $[0,1]$, meaning that for every $\epsilon'>0$ there is $J$ such that $|m_j(u)-m(u)|<\epsilon'$ for all $j\ge J$ and $u\in[0,1]$. For real $A,B$ with $0<A<B<1$, put $D_j=R_j^{-(B-A)}$, $d_j=\lfloor AN_j\rfloor$, $b_j=\lfloor BN_j\rfloor$, and $Q_{j,i}=Q(v_j,d_j,i)$. Here $Q(v,d,i)=\{z:v_r+i_r2^{-d}\le z_r<v_r+(i_r+1)2^{-d}\text{ for every }r\}$. Write $c_{j,i}$ for its center and $\mu_{j,i}=(z\mapsto2^{d_j}(z-c_{j,i}))_\#(\rho_j(Q_{j,i})^{-1}\rho_j|_{Q_{j,i}})$. Assume $t(w-A)\le m(w)-m(A)$ for every $w\in[A,B]$. For every real $\epsilon,\delta_0>0$, eventually in $j$ one has $0<D_j\le1$ and $D_j\le\delta_0$. For every $i$ with $\rho_j(Q_{j,i})>0$, $\mu_{j,i}$ is a probability carried by $\overline B(0,k+2)$ and satisfies $\mu_{j,i}(B(y,r))\le D_j^{-\epsilon}r^t$ for every $y\in\mathbb R^{k+1}$ and $D_j\le r\le1$. Moreover, for $\rho_j$-almost every $z$, the unchanged measure $\lambda_{j,z}$ has total mass at most one, is carried by $S^k$, and satisfies $\lambda_{j,z}(B(w,r))\le D_j^{-\epsilon}r^q$ for every $w\in S^k$ and $D_j\le r\le1$. When $q=k-1$, it also satisfies $\lambda_{j,z}\{w\in S^k:|\langle w,v\rangle|\le r\}\le D_j^{-\epsilon}r^\zeta$ for every unit vector $v$ and $D_j\le r\le1$.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 5, Lemma 5.3 (prep:one-scale), proof paragraph beginning with the middle interval and D=R^(-(B-A)), from rescaling an a-cell and using (prep:contact-middle) for its conditional t-ball bound through conversion of the unchanged reverse-law cap loss and absorption of the fixed endpoint plate constant into a small D-power loss.

import Definitions.Def_FalconerPath_connect
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 5, Lemma 5.3, middle interval, first paragraph: rescale an a-cell,
use the contact-middle inequality and uniform profile convergence for its
conditional t-ball bound. The UNCHANGED reverse laws have D-small cap losses;
the fixed endpoint plate constant is absorbed at these scales. No bad set,
retained relation, or improved radial estimate is asserted here. -/
theorem middle_scale_preparation {k : ℕ}
    (s q ζ L a C t : ℝ)
    (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (herr : Tendsto (fun j => (X j).err) atTop (𝓝 0))
    (m : ℝ → ℝ)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ j ≥ J, ∀ u ∈ Icc (0:ℝ) 1,
      |(X j).m u-m u| < ε)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1)
    (hmiddle : ∀ w ∈ Icc A B, t*(w-A) ≤ m w-m A)
    (ε δ₀ : ℝ) (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∀ᶠ j in atTop,
      let D := (scale (X j).N)^(-(B-A))
      let d := contactDepths (X j).N A B 1
      0 < D ∧ D ≤ 1 ∧ D ≤ δ₀ ∧
      (∀ i : Fin (k+1) → ℤ, 0 < (X j).ρ (dyadicCell (X j).v d i) →
        Probability (connectCellLaw (X j).ρ (X j).v d i) ∧
        Carried (connectCellLaw (X j).ρ (X j).v d i)
          (Metric.closedBall 0 ((k:ℝ)+2)) ∧
        ballBound (connectCellLaw (X j).ρ (X j).v d i) t (D^(-ε)) D) ∧
      (∀ᵐ z ∂(X j).ρ,
        Subprobability (reverseDirection (X j).ν (X j).G z) ∧
        Carried (reverseDirection (X j).ν (X j).G z) (unitSphere (k+1)) ∧
        capBound (reverseDirection (X j).ν (X j).G z) q (D^(-ε)) D ∧
        (q = (k:ℝ)-1 →
          plateBound (reverseDirection (X j).ν (X j).G z) ζ (D^(-ε)) D)) := by sorry
end FalconerPath
