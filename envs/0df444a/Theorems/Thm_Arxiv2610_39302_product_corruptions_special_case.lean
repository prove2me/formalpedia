-- Prove2me | Theorems.Thm_Arxiv2610_39302_product_corruptions_special_case
-- name    : Arxiv2610_39302.product_corruptions_special_case
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:05:35.052543+00:00
-- url     : https://prove2.me/theorems/7786d725-4cb0-5471-b413-6daff48431fd
-- title:
--   Theorem 4, special cases: product corruptions
-- statement:
--   Let $Z$ be a finite world with $p>0$, let observations be $(z,\nu)$ with nuisance $\nu\sim q$ on a finite set $N$, $q>0$, and let $W$ be the bad-view law of the product corruption $\Gamma=A\otimes B$ of Proposition 3, with $A,B$ row-stochastic with stationary laws $p,q$. Let $1\le k\le|Z|-1$. Then, in the notation of Theorem 4 and Proposition 3:
--
--   1. $\varepsilon=0$;
--   2. the induced world kernel is $\pi_W=A^\top D_pA$, so its eigenvalues are the $\alpha_i$;
--   3. if $|N|\ge2$: $\eta=\beta_1$; the gap condition $\delta>0$ reads
--   $$\alpha_k>\max(\alpha_{k+1},\beta_1);$$
--   and this holds exactly when the separation assumption $\xi_k>\xi_{k+1}$ of Proposition 3 holds together with $r=0$.
--
--   **Formalization Note** $\alpha_{k+1}=-\infty$ when $k+1=|Z|$. The paper's statement that the special case is "exactly the separation assumption of Proposition 3 together with $r=0$" is item 3's last equivalence.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c061 (a); Appendix A.4, formal Theorem 4, paragraph 'Special cases and scope', PDF p. 22

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem product_corruptions_special_case {Z N : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype N] [DecidableEq N] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (q : N → ℝ) (hq : ∀ ν, 0 < q ν) (hq1 : ∑ ν, q ν = 1)
    (A : Matrix Z Z ℝ) (hA : IsStationaryStochastic p A)
    (B : Matrix N N ℝ) (hB : IsStationaryStochastic q B)
    (hk : 1 ≤ k) (hkZ : k + 1 ≤ Fintype.card Z) :
    mixNorm (prodLaw p q) Prod.fst (badViewLaw p q A B) = 0 ∧
    inducedKernel Prod.fst (badViewLaw p q A B) = twoCorruptLaw p A ∧
    (2 ≤ Fintype.card N →
      nuisanceTop (prodLaw p q) Prod.fst (badViewLaw p q A B) = (corrEig q B 1 : EReal) ∧
      (0 < worldGap (prodLaw p q) Prod.fst (badViewLaw p q A B) k ↔
        max (extEig p (twoCorruptLaw p A) (k + 1)) (corrEig q B 1 : EReal) <
          (corrEig p A k : EReal)) ∧
      (max (extEig p (twoCorruptLaw p A) (k + 1)) (corrEig q B 1 : EReal) <
          (corrEig p A k : EReal) ↔
        xi p q A B (k + 1) < xi p q A B k ∧ nuisanceCount p q A B k = 0)) := by sorry

end Arxiv2610_39302
