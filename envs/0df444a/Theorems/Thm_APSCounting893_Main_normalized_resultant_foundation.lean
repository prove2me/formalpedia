-- Prove2me | Theorems.Thm_APSCounting893_Main_normalized_resultant_foundation
-- name    : APSCounting893.Main.normalized_resultant_foundation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:33:49.076467+00:00
-- url     : https://prove2.me/theorems/398d6dfd-29a4-4460-9355-fcda9e6c03b1
-- title:
--   Normalized integer resultant: existence and characteristic-zero base change
-- statement:
--   Let $d_0,\ldots,d_n$ be positive integers. There exists a universal polynomial with integer coefficients that is normalized to be $1$ on the diagonal pure-power system and is irreducible over $\mathbb C$, and whose vanishing exactly detects a common nonzero complex root.
--
--   Every integer polynomial satisfying these defining properties has, over every algebraically closed field $K$ of characteristic zero, the exact root criterion
--
--   $$\operatorname{Res}(G_0,\ldots,G_n)=0\quad\Longleftrightarrow\quad\exists x\in K^{n+1}\setminus\{0\}:G_i(x)=0\text{ for every }i,$$
--
--   for homogeneous forms $G_i$ of degrees $d_i$. This establishes the existence and base-change specification required to use the selected universal resultant over the valued-series fields in Lemma 5.2.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 5.1, pp. 20–21, Lemma 5.2 and Remark 5.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. Andrews, Garg and Schost, Hilbert’s Nullstellensatz is in the Counting Hierarchy, arXiv:2602.17904, https://arxiv.org/pdf/2602.17904, Definition 4.1, pp. 22–23 (existence, normalization, irreducibility and integral universal coefficients).

import Definitions.Def_APSCounting893_Main_Resultant
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.normalized_resultant_foundation
    {n : ℕ} (d : Fin (n+1) → ℕ) (hd : ∀ i, 0 < d i) :
    (∃ R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ, ResultantVNP.IsMultivariateResultant d R) ∧
    (∀ (R : MvPolynomial (ResultantVNP.CoeffVar d) ℤ) (hR : ResultantVNP.IsMultivariateResultant d R)
      (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
      (G : Fin (n+1) → MvPolynomial (Fin (n+1)) K) (hG : ∀ i, (G i).IsHomogeneous (d i)),
      MvPolynomial.eval₂ (Int.castRingHom K)
        (fun v : ResultantVNP.CoeffVar d => (G v.1).coeff v.2.1) R = 0 ↔
        ∃ x : Fin (n+1) → K, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (G i) = 0) := by sorry
