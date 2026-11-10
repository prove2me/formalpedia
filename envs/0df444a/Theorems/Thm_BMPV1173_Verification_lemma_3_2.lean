-- Prove2me | Theorems.Thm_BMPV1173_Verification_lemma_3_2
-- name    : BMPV1173.Verification.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:55.988207+00:00
-- url     : https://prove2.me/theorems/6d45d7ec-a8dd-43f3-944b-3780c6309f5a
-- title:
--   Lemma 3.2 — both OV and spurious-error inequalities
-- statement:
--   For every $n\ge2$, the explicit maps between an indexed single-list OV input and spurious-one verification errors give
--   $$Q(\mathrm{OV}_n)\le Q(\mathrm{BMPV}^{\ge}_n)\le Q(\mathrm{OV}_{2n+2}).$$
--   The converse self-product verification uses $(X,X^T,J_n)$ and accepts the complement of OV. The forward construction has rows $(A_i,e_i,1,0)$ and $(B_j^T,\overline C_j^T,0,1)$, followed by two all-one rows. It accepts OV exactly when verification has a spurious-one error. Both complement identities, both inequalities and the exact dimension $2n+2$ are included.
--
--   Differences from the source:
--   - encoding: bit entries indexed by [n] → Boolean functions on Fin n, with a matrix selector when needed; reason: the index bijection preserves every bit and every input instance
--   - encoding: both query inequalities obtained by oracle reductions → explicit constant-or-one-entry maps and predicate identities together with exact ENat least-query inequalities; reason: the complemented C block and the guard and filler rows preserve all source inputs; no one-hot oracle convention is substituted
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, Lemma 3.2, printed p.17 = PDF p.17.

import Definitions.Def_BMPV1173_Verification_Reductions

namespace BMPV1173.Verification

/-- Both complementary reductions and both inequalities, Lemma 3.2, p.17. -/
theorem lemma_3_2 (n : ℕ) (hn : 2 ≤ n) :
    (∀ x : VectorInput n,
      bmpvGE (evalMap (orthogonalVerificationMap n) x) = !(ov x)) ∧
    (∀ x : VerificationInput n,
      ov (evalMap (verificationOrthogonalMap n (by omega)) x) = !(bmpvGE x)) ∧
    qOV n ≤ qBMPVGE n ∧ qBMPVGE n ≤ qOV (2*n+2) := by sorry

end BMPV1173.Verification
