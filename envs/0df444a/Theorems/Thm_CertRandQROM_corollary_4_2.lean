-- Prove2me | Theorems.Thm_CertRandQROM_corollary_4_2
-- name    : CertRandQROM.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:38.41119+00:00
-- url     : https://prove2.me/theorems/535ae24f-32f2-4537-a9d1-e38867155c94
-- title:
--   Corollary 4.2 — total query norms move by at most $2Q\sum_{X}\tilde w(h)$ under $H\oplus X$
-- statement:
--   For any oracle $h$, any set $X$ of inputs and any input $u$,
--
--   $$
--   \big|\tilde w_u(h)-\tilde w_u(h\oplus X)\big|\le 2Q\cdot\sum_{u'\in X}\tilde w_{u'}(h). \tag{2}
--   $$
--
--   Equation (2) is the only property of query norms used in the reprogramming lemma (Lemma 4.3).
--
--   Differences from the source:
--   - generalization: inputs (i, x) ∈ [n] × Σ → inputs u of any finite type U; reason: taking U = Fin n × Σ gives the paper's statement
--   - generalization: A parametrized by Q ≥ 1 (§3.2) → any Q : ℕ, including Q = 0; reason: for Q ≥ 1 it is the paper's statement; Q = 0 is an extra trivial case
--   - encoding: a quantum query algorithm of §3.2 (registers (R_Q, R_A), unitaries, measurement M) → QueryAlg: query register exactly U, any finite work register W, unitaries U_1..U_Q, POVM; reason: the paper's model; a POVM includes every projective measurement and the inputs (1^λ, 1^{h∞}) are absorbed into the initial state
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Corollary 4.2, equation (2), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_CertRandQROM_queryNorm
import Definitions.Def_CertRandQROM_flipOn

namespace CertRandQROM

/-- **Corollary 4.2, equation (2)** (Coladangelo et al., arXiv:2608.31112 (sha256 b75095a2…),
p.18): for any oracle `h`, any set `X` of inputs and any input `u`,
`|w̃_u(h) − w̃_u(h ⊕ X)| ≤ 2Q · Σ_{u' ∈ X} w̃_{u'}(h)`. -/
theorem corollary_4_2 {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) (X : Finset U) (u : U) :
    |totalQueryNorm A h u - totalQueryNorm A (flipOn h X) u| ≤
      2 * (Q : ℝ) * ∑ u' ∈ X, totalQueryNorm A h u' := by sorry

end CertRandQROM
