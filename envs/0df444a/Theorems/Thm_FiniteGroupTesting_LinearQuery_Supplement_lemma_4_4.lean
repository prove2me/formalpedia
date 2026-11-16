-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_4_4
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:20:22.999657+00:00
-- url     : https://prove2.me/theorems/18f07a37-4058-4ac7-b75e-1066725c23ba
-- title:
--   Lemma 4.4 — True marked candidate and located values
-- statement:
--   Let $G$ be a finite group, let $\theta:G\to H$ be a group isomorphism, and choose visible generator labels $s_i$ and a dictionary start $d_0$. Compute the syntactic inverse candidates and the dictionary using any signed dictionary word. Mark $H$ by $\rho=\theta(d_0)$ and $a_i=\theta(s_i)$. Its dictionary equality pattern is identical to the visible one. For any common locator word,
--   $$\Psi_H(x)\text{ defined}\quad\Longrightarrow\quad\Psi_H(x)=\theta(x).$$
--   Thus the true candidate is retained by the dictionary test and is correctly interpreted at every located point, without a spectral assumption.
--
--   Differences from the source:
--   - generalization: an isomorphism onto an enumerated representative → an isomorphism onto any target group; reason: the statement uses only the isomorphism; every enumerated representative is an instance
--   - encoding: fixed parenthesized inverse expressions and a locator undefined on a miss → binary-power expressions, lists including time zero, and Option-valued locators; reason: these compute exactly the prescribed expressions and first-hit values, including arbitrary words
--   - encoding: a genuine input group table ([n],*) → an arbitrary finite group G with its own multiplication; reason: every genuine input table is such a group, and the conclusion uses only its multiplication
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 28, Lemma 4.4

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_Dictionary

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_4_4 {G H : Type} [Group G] [Fintype G] [DecidableEq G]
    [Group H] [DecidableEq H] {k : ℕ} (s : Fin k → G) (d₀ : G)
    (ξ σ : List (Signed k)) (θ : G ≃* H) :
    let u := visibleSigned (· * ·) (Fintype.card G) s
    let a := fun i => θ (s i)
    let ds := walk (· * ·) u d₀ ξ
    let hs := walk (· * ·) (signedMark a) (θ d₀) ξ
    equalityPattern ds hs ∧
      ∀ x h, locator (· * ·) u ds hs a σ x = some h → h = θ x := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
