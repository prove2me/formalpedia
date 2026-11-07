-- Prove2me | Theorems.Thm_DetANN_lemma_6_1
-- name    : DetANN.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:25.599954+00:00
-- url     : https://prove2.me/theorems/48e550c4-e744-4457-873e-19c297528585
-- title:
--   Lemma 6.1, p.14 — $\mathbb E|\sum_{\ell=1}^LX_\ell|^{2p}\le(CpL)^pv^{2p}$ for centered squared Rademacher sums
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $Y=\sum_ra_r\sigma_r$ for real coefficients $a_r$ (finitely many) and independent uniform signs $\sigma_r$, put $v=\sum_ra_r^2$ and $X=Y^2-v$, and let $X_1,\dots,X_L$ be independent copies of $X$. Then for every integer $1\le p\le L$,
--
--   $$\mathbb E\Big|\sum_{\ell=1}^LX_\ell\Big|^{2p}\le(CpL)^p\,v^{2p}.$$
--
--   It is the moment estimate that makes the expected potential (24) small.
--
--   Differences from the source:
--   - encoding: independent copies X₁, …, X_L and the expectation → L independent rows of signs σ : Fin L → R → Bool, and the uniform average over all of them; |·|^{2p} written (·)^{2p}; reason: the rows give L independent copies of X; an even power equals the power of the absolute value
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Lemma 6.1, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN

/-- **Lemma 6.1** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), p.14).
Let `Y = ∑_r a_r σ_r` with independent uniform signs `σ_r`, `v = ∑_r a_r²` and `X = Y² − v`. If
`X₁, …, X_L` are independent copies of `X`, then for every integer `1 ≤ p ≤ L`,
`E|∑_ℓ X_ℓ|^{2p} ≤ (C p L)^p v^{2p}`, where `C` is an absolute constant.

**Formalization Note.** `C > 0` is chosen before the index set `R`, the coefficients, `L` and `p`.
The `L` independent copies are realized by `L` independent rows of signs `σ : Fin L → R → Bool`, and
the expectation is the uniform average over all such `σ`; `|·|^{2p} = (·)^{2p}`. -/
theorem lemma_6_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Type) [Fintype R] [DecidableEq R] (a : R → ℝ) (L p : ℕ),
      1 ≤ p → p ≤ L →
        (Fintype.card (Fin L → R → Bool) : ℝ)⁻¹ *
            ∑ σ : Fin L → R → Bool,
              (∑ ℓ : Fin L, ((∑ r, a r * signOf (σ ℓ r)) ^ 2 - ∑ r, a r ^ 2)) ^ (2 * p) ≤
          (C * p * L) ^ p * (∑ r, a r ^ 2) ^ (2 * p) := by sorry

end DetANN
