-- Prove2me | Theorems.Thm_DetCCHard_lemma_7_1
-- name    : DetCCHard.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:37:41.550949+00:00
-- url     : https://prove2.me/theorems/1e330830-aa8b-4641-8ae3-e4d5911b2943
-- title:
--   Lemma 7.1 — exactly $D$-wise independent rational tuple lists of size $(1+qm)^D$ in polynomial time
-- statement:
--   Fix an integer independence order $D \ge 1$. Given normalized rational weights $\mu$ on an alphabet of size $m$ and an integer $q \ge 1$, a deterministic algorithm constructs an exactly $D$-wise independent tuple list $\mathrm{Code}_D(q, \mu)$ with marginal $\mu$ and a label set of size at most
--   $$
--   (1 + qm)^D .
--   $$
--   For fixed $D$, the construction time, total output length and rational-weight bit lengths are polynomial in $q$, $m$ and the binary encoding length of $\mu$.
--
--   These lists are what make each round of the deterministic reduction polynomial-time.
--
--   **Formalization Note** One string function per $D$, polynomial-time in the sense of the published `CookPvsNP.PolyTimeComputable`, maps the input encoding ($q$ in unary, weights as binary fractions) to the explicit list (each label's positive weight and decoded tuple). Output length and bit lengths are bounded by the running time.
--
--   Differences from the source:
--   - generalization: normalized rational weights μ (positive, by the convention of §4.2) → nonnegative weights summing to one; reason: positive weights are a special case; zero-weight letters are simply never needed
--   - encoding: time polynomial in q, m and the binary length of μ → PolyTimeComputable on the input encodeListInput q μ with q in unary; reason: with q in unary the input length is polynomially related to q, m and the binary length of μ
-- source:
--   Gaspers–He–Mackenzie, NP-Hardness and Additive Inapproximability of Deterministic Communication Complexity, arXiv:2508.05597 (held version, sha256 ad552d13…), Lemma 7.1, p.33

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_DetCCHard_IsWeight
import Definitions.Def_DetCCHard_TupleList
import Definitions.Def_DetCCHard_CodeSym
import Definitions.Def_DetCCHard_encodeListInput

namespace DetCCHard

/-- **Lemma 7.1 (Small rational tuple lists)** (Gaspers–He–Mackenzie, arXiv:2508.05597, held
version sha256 ad552d13…a4a03, Lemma 7.1, p.33). Fix an integer independence order `D ≥ 1`. Given
normalized rational weights `μ` on an alphabet of size `m` and an integer `q ≥ 1`, a deterministic
algorithm constructs an exactly `D`-wise independent tuple list `Code_D(q, μ)` with a label set of
size at most `(1 + qm)^D`. For fixed `D`, the construction time, total output length and
rational-weight bit lengths are polynomial in `q`, `m` and the binary encoding length of `μ`.

**Formalization Note** The algorithm is one string function per `D`, polynomial-time in the sense
of the published `CookPvsNP.PolyTimeComputable`, from `encodeListInput q μ` (`q` in unary, the
weights as binary numerator/denominator pairs) to `encodeListOutput ν z`, which lists every label's
weight and decoded tuple; the output *is* the encoding of the list. The labels are `Fin ℓ₀`, with
positive weights summing to one (Definition 4.4). Polynomial time in the input length bounds the
output length and the weights' bit lengths. -/
theorem lemma_7_1 (D : ℕ) (hD : 1 ≤ D) :
    ∃ f : List CodeSym → List CodeSym, CookPvsNP.PolyTimeComputable f ∧
      ∀ (m : ℕ) (μ : Fin m → ℚ), IsNormWeight μ → ∀ q : ℕ, 1 ≤ q →
        ∃ (ℓ₀ : ℕ) (ν : Fin ℓ₀ → ℚ) (z : Fin ℓ₀ → Fin q → Fin m),
          0 < ℓ₀ ∧ IsWeight ν ∧ ExactlyIndepW ν z D μ ∧ ℓ₀ ≤ (1 + q * m) ^ D ∧
            f (encodeListInput q μ) = encodeListOutput ν z := by sorry

end DetCCHard
