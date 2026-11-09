-- Prove2me | Theorems.Thm_ContiguousCake597_Approximate_lemma_3
-- name    : ContiguousCake597.Approximate.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:51.228307+00:00
-- url     : https://prove2.me/theorems/4bc0a8a9-9597-44c9-b0e8-e7b90dddfa5b
-- title:
--   Lemma 3 — exact and approximate PPAD membership
-- statement:
--   For all normalized nonnegative explicit rational piecewise-constant density inputs, finding a complete contiguous envy-free allocation is in PPAD. Finding a contiguous $\varepsilon$-envy-free allocation is also in PPAD, with positive rational precision encoded in binary or unary. In each mode $m$,
--   $$\mathcal C_{m,\mathrm{general}}\in\mathrm{PPAD}.$$
--   The answer relation is verifiable by a uniform polynomial-time Cook Turing machine. There is an exponent $k$ for each fixed mode, chosen before any input $s$, such that every valid input has some answer $t$ with $|t|\le |s|^k+k$. This is an existence bound on short witnesses, not a bound on every permitted representation of an answer.
--
--   This is the membership foundation for the classification. Exact mode uses rational cuts and zero envy tolerance, separately from the positive-precision input modes.
--
--   Differences from the source:
--   - encoding: PPAD membership and the preceding polynomial-size and verification assertions → the published PPAD predicate, together with explicit polynomial verification and short-witness existence in exact, binary and unary modes; reason: the imported PPAD definition alone does not include the verifier requirement; all clauses occur in §2.1
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 4 (PDF 5), Lemma 3 and preceding §2.1 paragraphs

import Definitions.Def_ContiguousCake597_Approximate_Analysis

namespace ContiguousCake597.Approximate

/-- Lemma 3, printed p.4 (PDF 5), including the polynomial witness and
verification requirements in the preceding paragraph. Binary accuracy is unrestricted. -/
theorem lemma_3 :
    (∀ mode : Precision, CakeProblem mode false ∈ QuasiStrictNE.PPAD) ∧
    (∀ mode : Precision,
      CookPvsNP.checkLang (CakeProblem mode false).answer ∈
        CookPvsNP.P (Option (Bool ⊕ Bool))) ∧
    (∀ mode : Precision, ∃ k : ℕ, ∀ s : List Bool,
      (CakeProblem mode false).valid s → ∃ t : List Bool,
        t.length ≤ s.length ^ k + k ∧ (CakeProblem mode false).answer s t) := by sorry

end ContiguousCake597.Approximate
