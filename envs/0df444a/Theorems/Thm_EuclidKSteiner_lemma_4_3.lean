-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_4_3
-- name    : EuclidKSteiner.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:19:58.965023+00:00
-- url     : https://prove2.me/theorems/bb579072-1bc3-4b11-806a-71de2729bcd8
-- title:
--   Lemma 4.3 — at most $\sum_{h\le 2b}4^{h-1}2^h$ templates, enumerated in $2^{O(b)}$ time
-- statement:
--   1. For all bounds $b,k$, every set of pairwise non-isomorphic augmented tree templates for $(b,k)$ (isomorphism preserving the root, child orders and roles) has at most
--   $$\sum_{h=1}^{2b}4^{h-1}\,2^h$$
--   elements; in particular there are $2^{O(b)}$ templates.
--   2. There are a deterministic real-RAM program and a constant $C>0$ such that, on input $(b,k)$, the program halts within $C\cdot2^{Cb}$ steps and outputs a list of template codes that contains every template for $(b,k)$ and only such templates.
--
--   The enumeration is the outer loop of the algorithm of Theorem 1.1.
--
--   **Formalization Note** The machine is the published real RAM restricted to admissible programs (rational literals, no random draws). Templates are their parenthesis codes; the output format is the number of codes followed by the codes.
--
--   Differences from the source:
--   - reading: there are 2^{O(b)} templates up to isomorphism → every set of distinct template codes for (b, k) has at most Σ_{h=1}^{2b} 4^{h−1}·2^h elements; reason: the count of the printed proof, which is a 2^{O(b)} bound
--   - encoding: templates up to isomorphism preserving root, child orders and roles → parenthesis-word codes with role lists (Template); reason: codes are in bijection with isomorphism classes of rooted ordered role-labelled trees
--   - encoding: they can all be enumerated in 2^{O(b)} time → an admissible MatMulTimeLP.RealRAM program and C > 0, fixed before (b, k), halting with t + 1 ≤ C·2^{C·b} and outputting a list of codes containing exactly the templates for (b, k); reason: O-notation with the constant before the input; the real-RAM model of p.3
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Layouts

namespace EuclidKSteiner

/-- **Lemma 4.3 (Enumerating augmented tree templates).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Lemma 4.3, p.16 (PDF p.18): "For given bounds b, k, there are 2^{O(b)} augmented tree
templates up to isomorphism preserving the root, child orders, and roles. They can all be enumerated
in 2^{O(b)} time."

1. (Count.) For all `b, k`, every set of pairwise distinct template codes satisfying Definition 4.2
   for `(b, k)` has at most `∑_{h=1}^{2b} 4^{h−1}·2^h` elements.
2. (Enumeration.) There are an admissible real-RAM program and `C > 0` such that on input `(b, k)`
   and every tape the run halts at a step `t` with `t + 1 ≤ C·2^{C·b}` and outputs a list of template
   codes containing every template for `(b, k)` and only such templates.

**Formalization Note** A template is its parenthesis-word code with its roles (`Template`); codes
are in bijection with templates up to isomorphism preserving the root, child orders and roles, so a
`Finset` of codes is a set of pairwise non-isomorphic templates. The count is the one of the proof
(at most `4^{h−1}` parenthesis words and `2^h` role assignments for `h` vertices), a constant inside
`2^{O(b)}`. The output format is `Template.encodeList`. -/
theorem lemma_4_3 :
    (∀ (b k : ℕ) (𝒯 : Finset Template), (∀ T ∈ 𝒯, T.IsTemplateFor b k) →
      𝒯.card ≤ ∑ h ∈ Finset.Icc 1 (2 * b), 4 ^ (h - 1) * 2 ^ h) ∧
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (b k : ℕ) (ω : MatMulTimeLP.Tape), ∃ t : ℕ,
        MatMulTimeLP.HaltsAt A (boundsLayout b k) ω t ∧
        (t : ℝ) + 1 ≤ C * (2 : ℝ) ^ (C * b) ∧
        ∃ Ts : List Template, OutputIs A (boundsLayout b k) ω t (Template.encodeList Ts) ∧
          (∀ T ∈ Ts, T.IsTemplateFor b k) ∧ ∀ T : Template, T.IsTemplateFor b k → T ∈ Ts := by sorry

end EuclidKSteiner
