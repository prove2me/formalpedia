-- Prove2me | Theorems.Thm_APSCounting893_Main_projective_incidence_relation_degree_bound
-- name    : APSCounting893.Main.projective_incidence_relation_degree_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T13:48:56.728036+00:00
-- url     : https://prove2.me/theorems/17145363-e9fb-46b8-84f9-d8b3a87fbe0d
-- title:
--   Degree bound for a projective incidence relation
-- statement:
--   Let $F:\mathbb C^n\to\mathbb C^m$ have image closure of dimension $1\le r<m$, suppose the origin is absent from that closure, and put $d=\max(1,\deg f_i)$. Let $W$ be the affine cone closure
--
--   $$W=\overline{\{sF(x):s\in\mathbb C,\ x\in\mathbb C^n\}}^{\mathrm{Zar}}.$$
--
--   Fix a coordinate $j$ for which $f_j\ne0$. For $z\in W$ and an $(r+1)\times m$ matrix $B$, define
--
--   $$A_{i,l}=z_jB_{i,l}-\left(\sum_t z_tB_{i,t}\right)\mathbf1_{l=j}.$$
--
--   There exists a nonzero polynomial $q$ in the entries of $A$ satisfying
--
--   $$\deg q\le(r+1)d^r,\qquad q(A)=0\quad\text{for all }z\in W\text{ and }B.$$
--
--   Every row of this parametrized matrix annihilates $z$. This is the incidence-relation form of the Chow-form degree bound used to construct the output-projection certificate. The cone and the incidence matrices are actual polynomial constructions; no avoidance property is assumed.
-- source:
--   Jeronimo, Krick, Sabia and Sombra, The computational complexity of the Chow form, arXiv:math/0210009, Section 1.1, pp.6–7 (incidence hypersurface and degree deg(V) in each coefficient block), https://arxiv.org/pdf/math/0210009#page=6; applied to the origin projection in Guo, Saxena and Sinhababu, Theory of Computing 15(16), 2019, proof of Theorem 4.6, p.21, https://theoryofcomputing.org/articles/v015a016/v015a016.pdf; polynomial-image degree bound there is at most d^r. This is the incidence relation underlying Agarwal–Hari–Pandey–Shukla, STOC 2027 submission #893, Theorem 3.13 and Proposition 3.14, pp.13–14, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_RandomReduction
set_option autoImplicit false
open MvPolynomial APSCounting893.Main

theorem APSCounting893.Main.projective_incidence_relation_degree_bound
    {n m r : ℕ} (F : PolynomialMap ℂ n m)
    (hr : 0 < r) (hrm : r < m)
    (hdim : RSCapacity.algDim (imageClosure F) = ((r : ℕ∞) : WithBot ℕ∞))
    (h0 : ¬ hasAPS F) (j : Fin m) (hj : F j ≠ 0) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin m) ℂ,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*(inputDegree F)^r ∧
      ∀ z ∈ imageClosure (fun i : Fin m => MvPolynomial.X (0 : Fin (n+1)) * MvPolynomial.rename Fin.succ (F i)),
        ∀ B : Fin (r+1) × Fin m → ℂ,
          eval (fun a => z j*B a - (∑ t : Fin m, z t*B (a.1,t))*(if a.2=j then 1 else 0)) q = 0 := by sorry
