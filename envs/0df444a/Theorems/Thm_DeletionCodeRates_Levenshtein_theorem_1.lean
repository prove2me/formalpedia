-- Prove2me | Theorems.Thm_DeletionCodeRates_Levenshtein_theorem_1
-- name    : DeletionCodeRates.Levenshtein.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:20:44.277857+00:00
-- url     : https://prove2.me/theorems/9a9ed12b-adda-494d-92cd-5eaebf0b5328
-- title:
--   Theorem 1 — improving the Levenshtein rate bound
-- statement:
--   For $0<\delta<1/2$, let
--   $$R^{(1)}_{\mathrm{del}}(\delta)=\sup_{x,y>0,\ x(1+y)<1}\big\{2\log_2(1+y)-(1-\delta)\log_2\lambda^{(1)}_{\mathrm{del}}(x,y)+2\delta\log_2x\big\},\qquad(2)$$
--   with $\lambda^{(1)}_{\mathrm{del}}(x,y)=1+y^2(1+3x)/(1-x)$. Then
--   $$\mathcal R^{(1)}_{2,\mathrm{del}}(\delta)\ge\big[R^{(1)}_{\mathrm{del}}(\delta)\big]_+.\qquad(3)$$
--   Furthermore, $R^{(1)}_{\mathrm{del}}(\delta)>R_{\mathrm{Lev}}(\delta)=1+\delta-2h_2(\delta)$.
--
--   Differences from the source:
--   - reading: R^{(1)}_{2,del}(δ), 'the supremum of achievable asymptotic rates' → supRateDel 2 δ 1: sSup of the R ≥ 0 such that for every ε > 0 and all large n some (0, ⌊δn⌋; 1)-list-decodable C_n ⊆ {0,1}^n has |C_n| ≥ 2^{n(R−ε)}; reason: the paper does not spell out the rate notion; codes for all large n (liminf) is the stronger reading for a lower bound and the one Lemma 8 delivers
--   - encoding: B(c; a, b), words obtainable by ≤ a insertions and ≤ b deletions → InsDelBall c a b: a common subsequence v with |c| ≤ |v| + b and |w| ≤ |v| + a; reason: delete first, then insert (as in the proof of Proposition 6); the same set
--   - encoding: [x]₊ → max x 0; reason: definition of the positive part
--   - encoding: the supremum in (2) → sSup of the image of D_del (RDel); reason: for 0 < δ < 1/2 the image is nonempty and bounded above by 1 − δ, so the real sSup is the paper's supremum
-- source:
--   Kiah, Wei, Zeng, Exponentially Larger Deletion-Correcting Codes and Constant-List-Decodable Insertion–Deletion Codes, arXiv:2609.21395 (PDF sha256 bc43cfa2…4d02), Theorem 1, p. 3 (PDF 5); proof §4.3, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_DeletionCodeRates_Levenshtein_Codes
import Definitions.Def_DeletionCodeRates_Levenshtein_RateFunctions

set_option autoImplicit false

namespace DeletionCodeRates.Levenshtein

/-- **Theorem 1** (improving the Levenshtein rate bound, p. 3). For `0 < δ < 1/2`, with
`R^{(1)}_del(δ) = sup_{x,y>0, x(1+y)<1} {2 log₂(1+y) - (1-δ) log₂ λ^{(1)}_del(x,y) + 2δ log₂ x}`
(2): `R^{(1)}_{2,del}(δ) ≥ [R^{(1)}_del(δ)]₊` (3); furthermore `R^{(1)}_del(δ) > R_Lev(δ)`. -/
theorem theorem_1 (δ : ℝ) (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    max (RDel δ) 0 ≤ supRateDel 2 δ 1 ∧ RLev δ < RDel δ := by sorry

end DeletionCodeRates.Levenshtein
