-- Prove2me | Theorems.Thm_DetSupportRank_DeterminantSupport_Supplement_theorem_1_2
-- name    : DetSupportRank.DeterminantSupport.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:17.510463+00:00
-- url     : https://prove2.me/theorems/1200b8ea-e1c5-4b87-ac09-c32b4433669b
-- title:
--   Theorem 1.2 — All algorithmic results: determinant rank, multisymmetric rank, analytic rank and Gowers norm
-- statement:
--   Let $n\ge d\ge3$. Over every field $F$, independently of any finiteness or characteristic assumption,
--   $$\operatorname{PR}(\det_n)=\begin{cases}n&n\text{ odd},\\n-1&n\text{ even}.\end{cases}$$
--   Furthermore, over every finite field $F_q$ of characteristic two,
--   $$\operatorname{PR}(E_{d,n})=\begin{cases}d&d\text{ odd},\\d-1&d\text{ even},\end{cases}\qquad \operatorname{AR}(E_{d,n})\le3,$$
--   and, for every nontrivial additive character $\chi$ of $F_q$,
--   $$\|\chi\circ e_{d,n}\|_{U^d}^{2^d}\ge q^{-3}.$$
--   This companion theorem contains all algorithmic conclusions of the paper in one statement. It supplements the unchanged determinant-support lower-bound goal, rather than replacing it.
--
--   Differences from the source:
--   - encoding: one-based indices in [n] → zero-based indices Fin n; reason: the increasing bijection preserves rows, columns and complements; paper i becomes r.val+1, also in signs
--   - encoding: integer minimum partition-decomposition length → the published partitionRank valued in ℕ∞; reason: it is the infimum of actual decomposition lengths and is finite and attained on the source domain; there is no changed rank notion
--   - encoding: analytic rank given by bias = q^(−AR) → EReal-valued negative logarithm, with nonpositive bias assigned +∞; reason: source multilinear inputs have positive bias; a finite upper bound cannot exploit log(0)=0; the extension changes no source instance
--   - encoding: Gowers norm raised to the power 2^d → real normalized cube average for every nontrivial AddChar F ℂ; reason: this is precisely the displayed power on the source domain; finite-field additive characters are unit-valued, with no character or field omitted
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), Theorem 1.2, p. 3 (PDF p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_PartitionRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_PolynomialMatrices
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_ElementaryMultisymmetric
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_AnalyticRank
import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_GowersPower

noncomputable section
open scoped BigOperators
universe u v

namespace DetSupportRank.DeterminantSupport.Supplement

/-- Theorem 1.2, p.3: the determinant clause is independent of the finite-field clauses. -/
theorem theorem_1_2 (n d : ℕ) (hnd : d ≤ n) (hd : 3 ≤ d) :
    (∀ (F : Type u) [Field F],
      partitionRank (determinantPolynomial F n) =
        if Odd n then (n : ℕ∞) else ((n - 1 : ℕ) : ℕ∞)) ∧
    (∀ (F : Type v) [Field F] [Fintype F] [CharP F 2],
      partitionRank (elementaryMultisymmetric F d n) =
        (if Odd d then (d : ℕ∞) else ((d - 1 : ℕ) : ℕ∞)) ∧
      analyticRank (fun x : (Fin d × Fin n) → F =>
        MvPolynomial.eval x (elementaryMultisymmetric F d n)) ≤ 3 ∧
      ∀ χ : AddChar F ℂ, χ ≠ 1 →
        (Fintype.card F : ℝ) ^ (-3 : ℤ) ≤
          gowersPower d (fun x : Fin n → F =>
            χ (MvPolynomial.eval x (MvPolynomial.esymm (Fin n) F d)))) := by sorry

end DetSupportRank.DeterminantSupport.Supplement
