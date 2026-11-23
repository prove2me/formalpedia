-- Prove2me | Theorems.Thm_CritWinSpin_p6b_6_3_lift_tm
-- name    : CritWinSpin.p6b_6_3_lift_tm
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:28:38.369234+00:00
-- url     : https://prove2.me/theorems/b87f8359-60ea-4a8e-b647-36f4832e44f6
-- title:
--   Uniform rational fixed-point approximation and Cook lift for the gadget reduction
-- statement:
--   Let $\rho$ be a single-site GHS spin law of type $p\ge2$, and let $A,C$ satisfy the gadget-parameter inequalities of (36). One deterministic polynomial-time Cook machine computes the entire rational lift used in Theorem 6.3(i). For all sufficiently large $n$, it chooses a rational approximation $\hat u_n$ to the positive fixed point $u=\phi'((\tau+\theta)u)$ satisfying (28), namely
--   $$
--   |\hat u_n-u|\le r^{-3},\qquad u/2\le\hat u_n\le2u,
--   $$
--   where $r=n^{pC}$ and $\theta=n^{A-(p-1)C}$. On the binary code of an admissible rational Ising instance $(J_0,h_0)$ on $n$ sites, the machine outputs the code of the lifted rational instance
--   $$
--   \tilde J=\left((\tau+\theta)I_n+\frac{J_0}{r\hat u_n^2}\right)\otimes\frac1r\mathbf1_r\mathbf1_r^\top,
--   \qquad \tilde h_{i,\alpha}=\frac{(h_0)_i}{r\hat u_n},
--   $$
--   together with $\hat u_n$, using the reindexing $[n]\times[r]\cong[nr]$.
--
--   This isolates the uniform numerical and encoding work in (30) and (36); the spectral and width conclusions of Theorem 6.3(i) are proved separately. The approximation can be chosen dyadic, so its rational encoding has polynomial size.
--
--   **Formalization Note.** `û_fn` records the same rational approximation returned by `liftF`; polynomial time is the published `CookPvsNP.PolyTimeComputable` one-tape model. The hypotheses of symmetry, zero diagonal, and width $\le n^w$ are those of Theorem 6.3.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), Theorem 6.3(i), pp.24–25; fixed-point approximation (28), p.20; lift (30), p.21; parameters (36), p.24.

import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
set_option autoImplicit false

/-- Uniform numerical approximation of the fixed point in (28), followed by evaluation of the
rational formulas (30) and (36). -/
theorem CritWinSpin.p6b_6_3_lift_tm (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ (liftF : Str → Str) (û_fn : ℕ → ℚ) (n₂ : ℕ),
        CookPvsNP.PolyTimeComputable liftF ∧
        (∀ n : ℕ, n₂ ≤ n → IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) (û_fn n)) ∧
        ∀ (n : ℕ) (H : Inst n), n₂ ≤ n → H.1.IsSymm → (∀ i, H.1 i i = 0) →
          width (castM H.1) (castV H.2) ≤ (n : ℝ) ^ w →
          liftF (encInst H) =
            tupleCode [encInst (liftInst S p Ac Cc H (û_fn n)), encRat (û_fn n)] := by sorry
