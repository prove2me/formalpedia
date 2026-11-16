-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_proposition_4_12
-- name    : DetSupportRank.DeterminantSupport.Supplement.proposition_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:36.142858+00:00
-- url     : https://prove2.me/theorems/6b6d0d66-e06b-42db-be75-9b195b33d6d2
-- title:
--   Proposition 4.12 — Analytic rank at most three and Gowers norm bound
-- statement:
--   Let $F_q$ be any finite field of characteristic two and $n\ge d\ge3$. Evaluate $E_{d,n}$ on all $d$ independent row vectors with the uniform distribution. Then
--   $$\operatorname{AR}(E_{d,n})\le3.$$
--   For every nontrivial additive character $\chi:F_q\to\mathbb C^\times$, the actual squarefree elementary symmetric polynomial also satisfies
--   $$\|\chi\circ e_{d,n}\|_{U^d}^{2^d}\ge q^{-3}.$$
--   Both conclusions are retained. This supports the analytic-rank and Gowers clauses of Theorem 1.2, with the full field cardinality $q=|F_q|$.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: analytic rank given by bias = q^(−AR) → EReal-valued negative logarithm, with nonpositive bias assigned +∞; reason: source multilinear inputs have positive bias; a finite upper bound cannot exploit log(0)=0; the extension changes no source instance
--   - encoding: Gowers norm raised to the power 2^d → real normalized cube average for every nontrivial AddChar F ℂ; reason: this is precisely the displayed power on the source domain; finite-field additive characters are unit-valued, with no character or field omitted
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Proposition 4.12, p. 13 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_ElementaryMultisymmetric
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_AnalyticRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_GowersPower

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Proposition 4.12, p.13, proved p.15: both conclusions and every nontrivial character. -/
theorem proposition_4_12 {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (n d : ℕ) (hnd : d ≤ n) (hd : 3 ≤ d) :
    analyticRank (fun x : (Fin d × Fin n) → F =>
        MvPolynomial.eval x (elementaryMultisymmetric F d n)) ≤ 3 ∧
      ∀ χ : AddChar F ℂ, χ ≠ 1 →
        (Fintype.card F : ℝ) ^ (-3 : ℤ) ≤
          gowersPower d (fun x : Fin n → F =>
            χ (MvPolynomial.eval x (MvPolynomial.esymm (Fin n) F d))) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
