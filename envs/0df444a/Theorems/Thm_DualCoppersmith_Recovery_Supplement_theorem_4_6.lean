-- Prove2me | Theorems.Thm_DualCoppersmith_Recovery_Supplement_theorem_4_6
-- name    : DualCoppersmith.Recovery.Supplement.theorem_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T06:36:10.044849+00:00
-- url     : https://prove2.me/theorems/01a36213-3b17-4b1f-a417-686bc9c2df53
-- title:
--   Theorem 4.6 — Recovery over a public modulus
-- statement:
--   Let $N\ge2$ be a public modulus (not assumed prime), $F=(f_1,\ldots,f_s)$ integer polynomials in $\ell\ge1$ variables with $\max_a\deg(f_a)\le d$ for an integer $d\ge1$, and $X_1,\ldots,X_\ell$ positive integer bounds. Fix integers $m,t\ge1$ with $t\ge dm$, and build the lattice $L_X^\perp\subset\mathbb R^n$ modulo $N^m$ from the total-degree shifts $g_{i,\beta}=N^{m-|i|}x^\beta F^i$, where $n=|T_t|$ and $\rho=\operatorname{lcm}\{X^\alpha:\alpha\in T_t\}$. Let $0<\beta\le1$, let $r\in\mathbb Z^\ell$ be a bounded target ($|r_i|<X_i$), and put $p=\gcd(N,f_1(r),\ldots,f_s(r))$ with $p\ge N^\beta$ and $q_0=N/p$. Write $v_r=((\rho/X^\alpha)r^\alpha)_\alpha$. Then:
--
--   1. The lattice meets the real line through $v_r$ exactly in the integer multiples of $q_0^m v_r$:
--   $$L_X^\perp\cap\mathbb Rv_r=\mathbb Z\,q_0^m v_r .$$
--   2. For every $\delta\ge1$ and every nonzero $w\in L_X^\perp$ with $\|w\|\le\delta^{2(n-1)}\lambda_1(L_X^\perp)$, if
--   $$\lambda_2(L_X^\perp)>\delta^{2(n-1)}\,q_0^m\,\|v_r\|,$$
--   then the constant coordinate $w_0$ is nonzero and $r_i=X_i\,w_{e_i}/w_0$ for every $i\in[\ell]$.
--
--   No primality of $N$ or of $p$ is required. The theorem extends the recovery guarantee of the base mission from a known prime to a composite public modulus whose relevant divisor is unknown: the target line is still isolated in the lattice, with primitive generator $q_0^m v_r$ in place of $v_r$, and a short reduced vector still reveals the root by coordinate ratios.
--
--   **Formalization Note** $\lambda_1$ is the published infimum of norms of nonzero lattice vectors and $\lambda_2$ the base mission's second successive minimum; $\|\cdot\|$ is the Euclidean norm. The real line $\mathbb Rv_r$ is the set of all real multiples $c\,v_r$, including irrational $c$. The constant coordinate is the monomial $x^0$, and $e_i$ is the coordinate of the monomial $x_i$. The hypotheses $0<\beta\le1$ and $p\ge N^\beta$ are kept exactly as in the source, although the conclusion does not depend on them.
--
--   Differences from the source:
--   - reading: "suppose reduction returns a nonzero vector w satisfying ‖w‖ ≤ δ^{2(n−1)} λ₁(L_X^⊥)" → for every nonzero w ∈ L_X^⊥ satisfying that bound; reason: the reduction output is a vector of the lattice being reduced and the page assumes nothing else about it; quantifying over all such vectors covers every reduction routine
--   - encoding: one-based variables and the ordered monomial set T_t → zero-based finite indices and a fixed equivalence enumerating all multi-indices of total degree at most t, with the constant and linear coordinates named explicitly; reason: reindexing preserves every coordinate and the Euclidean norm
--   - encoding: shifts with 1 ≤ |i| ≤ m and deg(x^β F^i) ≤ t → the same shifts with identically zero ones omitted; reason: a zero shift row imposes only 0 = 0, so K and L_X^⊥ are unchanged
--   - encoding: p = gcd(N, f_1(r), …, f_s(r)) and q_0 = N/p → a natural-number gcd of N and the absolute values |f_a(r)|, and exact natural division N/p; reason: gcd is insensitive to signs and p ∣ N, so both values are the source's
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 16, Theorem 4.6 (PDF p. 17)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Supplement_PublicModulus
import Definitions.Def_DualCoppersmith_Recovery_Geometry
import Definitions.Def_RegevLWE_SmoothingLB_Lattice

set_option autoImplicit false

namespace DualCoppersmith.Recovery.Supplement

/-- Theorem 4.6, printed p. 16 / PDF p. 17: both conclusions, for every `δ ≥ 1`
    and every nonzero vector `w` of the lattice meeting the first-vector bound. -/
theorem theorem_4_6 (I : PublicInstance) (P : PublicParameters I)
    (beta : ℝ) (hbeta_pos : 0 < beta) (hbeta_le : beta ≤ 1)
    (d : ℕ) (hd : 1 ≤ d) (hdeg : ∀ a, (I.F a).totalDegree ≤ d) (htd : d * P.m ≤ P.t)
    (r : Fin I.ell → ℤ) (hr : IsBoxed I r)
    (hp : (I.N : ℝ) ^ beta ≤ (divisor I r : ℝ)) :
    ((pubScaledLattice I P : Set (LLLFactor.RedBasis.Vec (pubDimension I P))) ∩
        Set.range (fun c : ℝ => c • pubRootVector I P r) =
      Set.range (fun k : ℤ =>
        ((k : ℝ) * (cofactor I r : ℝ) ^ P.m) • pubRootVector I P r)) ∧
    ∀ (delta : ℝ), 1 ≤ delta →
      ∀ w ∈ pubScaledLattice I P, w ≠ 0 →
        ‖w‖ ≤ delta ^ (2 * (pubDimension I P - 1)) *
          RegevLWE.SmoothingLB.lambda1 (pubScaledLattice I P) →
        delta ^ (2 * (pubDimension I P - 1)) * (cofactor I r : ℝ) ^ P.m *
          ‖pubRootVector I P r‖ < secondMinimum (pubScaledLattice I P) →
        w (pubConstantIndex I P) ≠ 0 ∧
          ∀ i, (r i : ℝ) =
            (I.X i : ℝ) * w (pubLinearIndex I P i) / w (pubConstantIndex I P) := by sorry

end DualCoppersmith.Recovery.Supplement
