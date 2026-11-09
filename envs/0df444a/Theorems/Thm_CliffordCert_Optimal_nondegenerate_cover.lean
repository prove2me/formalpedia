-- Prove2me | Theorems.Thm_CliffordCert_Optimal_nondegenerate_cover
-- name    : CliffordCert.Optimal.nondegenerate_cover
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:59.652201+00:00
-- url     : https://prove2.me/theorems/8e52598f-3cb6-48f1-9024-cd55f58dde94
-- title:
--   Theorem 1 — nondegenerate cover and verified preprocessing
-- statement:
--   Let $(V,B)$ be a nondegenerate binary symplectic space of dimension $N$ and let $k$ be even, $2\le k\le N$. There is a list of nondegenerate $k$-subspaces satisfying
--   $$V=\bigcup_{i=1}^L S_i,\qquad L\le6\cdot2^{N-k}.$$
--   Given any ordinary cover with $L_0\le2\cdot2^{N-k}$ members, exhaustive coordinate search terminates at a $g$ satisfying $F(g)\le3L_0$, and the finite repair search returns a valid list with this bound. Every accepted coordinate change returns such a list. Independent uniform invertible-coordinate trials satisfy
--   $$\Pr(T>j)\le(7/9)^j,\qquad\Pr(T<\infty)=1,\qquad\mathbb ET\le9/2.$$
--   The accepted output is always checked. This finite preprocessing fixes a family before the unknown input is supplied; it makes no efficiency claim.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
--   - encoding: independent uniform GL trials and stopping time → uniform finite GL words, the no-acceptance prefix probabilities, their limit and extended tail-sum expectation; reason: finite prefixes specify the independent experiment and retain almost-sure termination and the full expectation bound
--   - encoding: finite deterministic search and repaired output → find? on exhaustive finite lists, with successful options and correctness as conclusions; reason: unlike a choice of a cover this specifies the search check and returned result
--   - generalization: Theorem 1 states a cover and terminating preprocessing → the preprocessing guarantee holds starting from every ordinary k-cover of size at most 2·2^(N−k); reason: the proof in §C.4 starts with an arbitrary Lemma 7 cover and uses only its coverage, dimensions and size; its chosen cover is an instance
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 5, Theorem 1, Eq. (1); §C.4 p. 14 (PDF p. 15) (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal ENat

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem nondegenerate_cover {N : ℕ} (B : Form N) (hB : IsSymplectic B)
    (k : ℕ) (hk : Even k) (hk2 : 2 ≤ k) (hkN : k ≤ N) :
    (∃ S : List (Submodule F₂ (Binary N)),
      IsGoodCover B k S ∧ S.length ≤ 6 * 2^(N-k)) ∧
    (∀ W : List (Submodule F₂ (Binary N)), IsKCover k W →
      W.length ≤ 2 * 2^(N-k) →
      (∃ g S, deterministicCoordinate B W = some g ∧ coordinateCheck B W g ∧
        repairedOutput B W g = some S ∧ IsGoodCover B k S ∧
        S.length ≤ 6*2^(N-k)) ∧
      (∀ g, coordinateCheck B W g → ∃ S,
        repairedOutput B W g = some S ∧ IsGoodCover B k S ∧
        S.length ≤ 6*2^(N-k)) ∧
      (∀ trials g, firstAccepted B W trials = some g → coordinateCheck B W g) ∧
      (∀ (gs : ℕ → Coordinates N) (j : ℕ),
        (j : ℕ∞) < stoppingTrial B W gs ↔ ∀ i < j, ¬ coordinateCheck B W (gs i)) ∧
      (∀ gs : ℕ → Coordinates N, (∃ j, coordinateCheck B W (gs j)) →
        ∃ S, stoppedOutput B W gs = some S ∧ IsGoodCover B k S ∧
          S.length ≤ 6*2^(N-k)) ∧
      (∀ j : ℕ, trialTail B W j ≤ (7/9 : ℝ)^j) ∧
      Filter.Tendsto (trialTail B W) Filter.atTop (nhds 0) ∧
      expectedTrials B W ≤ ENNReal.ofReal (9/2)) := by sorry
end CliffordCert.Optimal
