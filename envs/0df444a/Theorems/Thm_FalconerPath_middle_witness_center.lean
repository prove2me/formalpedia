-- Prove2me | Theorems.Thm_FalconerPath_middle_witness_center
-- name    : FalconerPath.middle_witness_center
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:50.886637+00:00
-- url     : https://prove2.me/theorems/44d3d152-c935-4401-8946-79f2e7907946
-- title:
--   Transfer of a center-direction tube cover to every source witness
-- statement:
--   Let $k\in\mathbb N$ and $s,q,\zeta,L,a,C\in\mathbb R$. For every $j\in\mathbb N$, let $X_j$ consist of $N_j\in\mathbb N$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$, a translation $v_j$, a real function $m_j$, an error $e_j\ge0$, and a Borel relation $G_j$. Assume $L,a>0$, both supports lie in $\overline B(0,L)$, and $\|x-z\|\ge a$ for every $x\in\operatorname{supp}\nu_j$ and $z\in\operatorname{supp}\rho_j$. The measure $\rho_j$ is carried by the half-open unit grid cell $Q(v_j,0,0)$. On $[0,1]$, $m_j$ is nondecreasing and $(k+1)$-Lipschitz, $m_j(0)=0$, and $m_j(u)\ge su-e_j$. Put $R_j=2^{N_j}$. For every $\ell\le N_j$ and cell $Q=Q(v_j,\ell,i)$ with positive mass, require $R_j^{-m_j(\ell/N_j)-e_j}\le\rho_j(Q)\le R_j^{-m_j(\ell/N_j)+e_j}$. For every $0\le\ell\le h\le N_j$ and nested cells $Q'=Q(v_j,h,i')\subseteq Q=Q(v_j,\ell,i)$ with $\rho_j(Q')>0$, require $R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))-e_j}\le\rho_j(Q')/\rho_j(Q)\le R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))+e_j}$. At $N_j=0$ real division uses $0/0=0$. Assume $G_j\subseteq\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$. Define $\lambda_{j,z}=(\pi_z)_\#(\nu_j|_{\{x:(x,z)\in G_j\}})$, where $\pi_z(x)=\|x-z\|^{-1}(x-z)$ with value zero at $x=z$. For $\rho_j$-almost every $z$, every $w\in S^k$ and every $2^{-N_j}\le u\le1$ with $u>0$ satisfy $\lambda_{j,z}(B(w,u))\le R_j^{e_j}u^q$. Also, for $\rho_j$-almost every $z$, every $v\in S^k$ and the same radii satisfy $\lambda_{j,z}\{w\in S^k:|\langle w,v\rangle|\le u\}\le[Cu^\zeta]_+$. Here $[u]_+=\max(u,0)$ in the extended nonnegative reals. These are the conditions encoded by $X_j\in\mathrm{RadialClassData}(k,s,q,\zeta,L,a,C)$. Assume $N_j\to\infty$. For real $A,B$ with $0<A<B<1$, put $D_j=R_j^{-(B-A)}$, $d_j=\lfloor AN_j\rfloor$, $b_j=\lfloor BN_j\rfloor$, and $Q_{j,i}=Q(v_j,d_j,i)$. Here $Q(v,d,i)=\{z:v_r+i_r2^{-d}\le z_r<v_r+(i_r+1)2^{-d}\text{ for every }r\}$. Write $c_{j,i}$ for its center and $\mu_{j,i}=(z\mapsto2^{d_j}(z-c_{j,i}))_\#(\rho_j(Q_{j,i})^{-1}\rho_j|_{Q_{j,i}})$. Assume $B<2A$ and fix real $K,c>0$. Write $\mathcal T_L(w,b,r)=\{y:\|y\|\le L,\ \operatorname{dist}(y,b+\mathbb Rw)\le r\}$ and let $\mathcal B(\mu,L,C,\delta,q,c)$ be the set of $w\in S^k$ for which some finite anchor set $F\subset\mathbb R^{k+1}$ has $\#F\le\delta^{-q-c}$ and $\mu(\bigcup_{b\in F}\mathcal T_L(w,b,C\delta))\ge\delta^c$. Eventually in $j$, for every $i$ with $\rho_j(Q_{j,i})>0$, every $x\in\operatorname{supp}\nu_j$, every $z\in Q_{j,i}\cap\operatorname{supp}\rho_j$, and every finite anchor set $F\subset\mathbb R^{k+1}$, if $\#F\le D_j^{-q-c}$ and $\mu_{j,i}(\bigcup_{b\in F}\mathcal T_{k+2}(\pi_{c_{j,i}}(x),b,KD_j))\ge D_j^c$, then $\pi_z(x)\in\mathcal B(\mu_{j,i},k+2,K+1,D_j,q,c)$.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 5, Lemma 5.3 (prep:one-scale), proof paragraph beginning with deletion of the pairs in (prep:witness-bad), through (prep:linearization-margin) and the center-direction robustness conclusion. B<2A gives R^(-A)=o(D), and recentering axes in the bounded rescaled ball allows arbitrary anchors before the width enlargement K+1.

import Definitions.Def_FalconerPath_connect
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 5, proof of Lemma 5.3, paragraph after (prep:witness-bad):
B<2A gives R^(-A)=o(D). Recenter tube axes in the bounded rescaled ball
and transfer a center-direction cover to ANY source witness, using width
K+1. Reverse directions are used consistently; tubes are unoriented.
This is only a geometric cover implication, with no angular mass bound. -/
theorem middle_witness_center {k : ℕ} (s q ζ L a C : ℝ)
    (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1) (hBA : B < 2*A)
    (K c : ℝ) (hK : 0 < K) (hc : 0 < c) :
    ∀ᶠ j in atTop,
      let D := (scale (X j).N)^(-(B-A))
      let d := contactDepths (X j).N A B 1
      ∀ i : Fin (k+1) → ℤ, 0 < (X j).ρ (dyadicCell (X j).v d i) →
      ∀ x ∈ (X j).ν.support, ∀ z ∈ dyadicCell (X j).v d i,
      z ∈ (X j).ρ.support → ∀ anchors : Finset (Space (k+1)),
        (anchors.card : ℝ) ≤ D^(-q-c) →
        ENNReal.ofReal (D^c) ≤ connectCellLaw (X j).ρ (X j).v d i
          (⋃ b ∈ anchors, tube ((k:ℝ)+2)
            (radial (connectCellCenter (X j).v d i) x) b (K*D)) →
        radial z x ∈ badDirections (connectCellLaw (X j).ρ (X j).v d i)
          ((k:ℝ)+2) (K+1) D q c := by sorry
end FalconerPath
