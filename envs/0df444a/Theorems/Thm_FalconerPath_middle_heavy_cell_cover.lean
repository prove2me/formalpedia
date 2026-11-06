-- Prove2me | Theorems.Thm_FalconerPath_middle_heavy_cell_cover
-- name    : FalconerPath.middle_heavy_cell_cover
-- status  : Open
-- author  : @dangnguyen
-- created : 2026-11-05T23:14:47.836357+00:00
-- url     : https://prove2.me/theorems/a5bc0f4c-a8a1-48bd-9a78-74c21bc5d705
-- title:
--   Tube cover domination of the full conditional heavy source set
-- statement:
--   Let $k\in\mathbb N$ and $s,q,\zeta,L,a,C\in\mathbb R$. For every $j\in\mathbb N$, let $X_j$ consist of $N_j\in\mathbb N$, probabilities $\nu_j,\rho_j$ on $\mathbb R^{k+1}$, a translation $v_j$, a real function $m_j$, an error $e_j\ge0$, and a Borel relation $G_j$. Assume $L,a>0$, both supports lie in $\overline B(0,L)$, and $\|x-z\|\ge a$ for every $x\in\operatorname{supp}\nu_j$ and $z\in\operatorname{supp}\rho_j$. The measure $\rho_j$ is carried by the half-open unit grid cell $Q(v_j,0,0)$. On $[0,1]$, $m_j$ is nondecreasing and $(k+1)$-Lipschitz, $m_j(0)=0$, and $m_j(u)\ge su-e_j$. Put $R_j=2^{N_j}$. For every $\ell\le N_j$ and cell $Q=Q(v_j,\ell,i)$ with positive mass, require $R_j^{-m_j(\ell/N_j)-e_j}\le\rho_j(Q)\le R_j^{-m_j(\ell/N_j)+e_j}$. For every $0\le\ell\le h\le N_j$ and nested cells $Q'=Q(v_j,h,i')\subseteq Q=Q(v_j,\ell,i)$ with $\rho_j(Q')>0$, require $R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))-e_j}\le\rho_j(Q')/\rho_j(Q)\le R_j^{-(m_j(h/N_j)-m_j(\ell/N_j))+e_j}$. At $N_j=0$ real division uses $0/0=0$. Assume $G_j\subseteq\operatorname{supp}\nu_j\times\operatorname{supp}\rho_j$. Define $\lambda_{j,z}=(\pi_z)_\#(\nu_j|_{\{x:(x,z)\in G_j\}})$, where $\pi_z(x)=\|x-z\|^{-1}(x-z)$ with value zero at $x=z$. For $\rho_j$-almost every $z$, every $w\in S^k$ and every $2^{-N_j}\le u\le1$ with $u>0$ satisfy $\lambda_{j,z}(B(w,u))\le R_j^{e_j}u^q$. Also, for $\rho_j$-almost every $z$, every $v\in S^k$ and the same radii satisfy $\lambda_{j,z}\{w\in S^k:|\langle w,v\rangle|\le u\}\le[Cu^\zeta]_+$. Here $[u]_+=\max(u,0)$ in the extended nonnegative reals. These are the conditions encoded by $X_j\in\mathrm{RadialClassData}(k,s,q,\zeta,L,a,C)$. Assume $N_j\to\infty$. For real $A,B$ with $0<A<B<1$, put $D_j=R_j^{-(B-A)}$, $d_j=\lfloor AN_j\rfloor$, $b_j=\lfloor BN_j\rfloor$, and $Q_{j,i}=Q(v_j,d_j,i)$. Here $Q(v,d,i)=\{z:v_r+i_r2^{-d}\le z_r<v_r+(i_r+1)2^{-d}\text{ for every }r\}$. Write $c_{j,i}$ for its center and $\mu_{j,i}=(z\mapsto2^{d_j}(z-c_{j,i}))_\#(\rho_j(Q_{j,i})^{-1}\rho_j|_{Q_{j,i}})$. Assume $B<2A$ and let $W>0$ be real. Define $\mathcal H_{\rho,Q,r,f}(x)=\{z\in Q\cap\operatorname{supp}\rho:\rho\{z'\in Q:\|\pi_x(z')-\pi_x(z)\|\le r\}>[f]_+\rho(Q)\}$ and $\mathcal T_L(w,y,r)=\{u:\|u\|\le L,\operatorname{dist}(u,y+\mathbb Rw)\le r\}$. There exists $K>0$ such that for every real $c>0$, eventually in $j$, every cell $Q_{j,i}$ with positive $\rho_j$-mass and every $x\in\operatorname{supp}\nu_j$ admit a finite anchor set $F$ with $\#F\le D_j^{-q-c}$ and
--   $$(\rho_j(Q_{j,i})^{-1}\rho_j|_{Q_{j,i}})\bigl(\mathcal H_{\rho_j,Q_{j,i},W2^{-b_j},D_j^{q+c/2}}(x)\bigr)\le\mu_{j,i}\left(\bigcup_{y\in F}\mathcal T_{k+2}(\pi_{c_{j,i}}(x),y,KD_j)\right).$$
--   The constant $K$ is chosen before $c$. The heavy-set comparison uses the whole source cell.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions, OpenAI Math Release preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf, Section 5, Lemma 5.3 (prep:one-scale), proof paragraph starting with Taylor expansion for two points in Q, through the perpendicular projection implication and the heavy projected grid-cell cover, ending with its tube count being less than D^(-q-c_1) for small D. B<2A absorbs the quadratic error, and the extra D^(-c/2) absorbs fixed covering constants and boundedly many neighbors.

import Definitions.Def_FalconerPath_connect
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FalconerPath
/-- Section 5, Lemma 5.3, from the Taylor expansion through the heavy
perpendicular grid-cell cover. B<2A absorbs R^(-2A) into R^(-B).
The O(D^(-q-c/2)) heavy cells (including boundedly many neighbors) use
at most D^(-q-c) tubes for sufficiently large j. The displayed domination
is for the FULL conditional source heavy set, not its pair-restricted fiber.
There is no robustness or small-mass conclusion in this child. -/
theorem middle_heavy_cell_cover {k : ℕ} (s q ζ L a C : ℝ)
    (X : ℕ → RadialClassData k s q ζ L a C)
    (hN : Tendsto (fun j => (X j).N) atTop atTop)
    (A B : ℝ) (hA : 0 < A) (hAB : A < B) (hB : B < 1) (hBA : B < 2*A)
    (W : ℝ) (hW : 0 < W) :
    ∃ K : ℝ, 0 < K ∧ ∀ c : ℝ, 0 < c → ∀ᶠ j in atTop,
      let D := (scale (X j).N)^(-(B-A))
      let d := contactDepths (X j).N A B 1
      let b := contactDepths (X j).N A B 2
      ∀ i : Fin (k+1) → ℤ, 0 < (X j).ρ (dyadicCell (X j).v d i) →
      ∀ x ∈ (X j).ν.support,
        ∃ anchors : Finset (Space (k+1)),
          (anchors.card : ℝ) ≤ D^(-q-c) ∧
          normalizedRestriction (X j).ρ (dyadicCell (X j).v d i)
            (connectHeavy (X j).ρ (dyadicCell (X j).v d i)
              (W*mesh b) (D^(q+c/2)) x) ≤
            connectCellLaw (X j).ρ (X j).v d i
              (⋃ y ∈ anchors, tube ((k:ℝ)+2)
                (radial (connectCellCenter (X j).v d i) x) y (K*D)) := by sorry
end FalconerPath
