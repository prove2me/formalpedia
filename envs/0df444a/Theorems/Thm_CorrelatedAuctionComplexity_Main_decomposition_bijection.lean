-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_decomposition_bijection
-- name    : CorrelatedAuctionComplexity.Main.decomposition_bijection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:46.636468+00:00
-- url     : https://prove2.me/theorems/b86cf9a6-fc35-4cf2-8bee-57ba5c2a3da5
-- title:
--   Lemma 19 — Polynomial bijection, equilibrium iff, and purity
-- statement:
--   Let $A$ be any normalized DFPA and $H_A$ its type-clone decomposition. The map $f(\sigma)_i(v)=\sigma_{(i,v)}$ is a bijection on legal real mixed profiles with inverse given by the reverse reindexing. The constructed decomposition is a well-formed HDFPA. Both profile transformations are polynomial-time on their explicit rational encodings. For every $\varepsilon\ge0$,
--
--   $$\sigma\text{ is an }\varepsilon\text{-NE of }H_A\quad\Longleftrightarrow\quad f(\sigma)\text{ is an }\varepsilon\text{-MBNE of }A.$$
--
--   Moreover $f$ preserves purity, and so does its inverse. The statement also records the inverse identities on the raw profile coordinates and the equivalence of legality; they express the asserted bijection without silently omitting a strategy constraint.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
--   - encoding: f and f⁻¹ computable in polynomial time → uniform polynomial-time maps on rational profile codes; H_A profiles list clone x_{i,v} in the same (bidder, sorted type, sorted bid) order as A-profiles; reason: H_A has no canonical bidder order in the source; with this order both maps are the coordinate reindexing the proof calls polynomially computable
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 19, p. 24 (PDF p. 24)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem decomposition_bijection :
    ∃ (f g : Bits → Bits), CookPvsNP.PolyTimeComputable f ∧ CookPvsNP.PolyTimeComputable g ∧
      ∀ (n : ℕ) (A : DFPA (Fin n)), A.WellFormed 1 →
        A.decomposition.WellFormed 1 ∧
        Function.Bijective A.profileForward ∧
        (∀ σ, A.profileInverse (A.profileForward σ) = σ) ∧
        (∀ β, A.profileForward (A.profileInverse β) = β) ∧
        (∀ σ, A.decomposition.Legal σ ↔ A.Legal (A.profileForward σ)) ∧
        (∀ σ : A.decomposition.RatProfile,
          f (encodeCloneProfile A σ) = encodeDProfile A (forwardRat A σ)) ∧
        (∀ β : A.RatProfile,
          g (encodeDProfile A β) = encodeCloneProfile A (inverseRat A β)) ∧
        (∀ (ε : ℝ), 0 ≤ ε → ∀ σ,
          A.decomposition.IsNE ε σ ↔ A.IsMBNE ε (A.profileForward σ)) ∧
        (∀ σ, A.decomposition.Legal σ → A.decomposition.Pure σ → A.Pure (A.profileForward σ)) ∧
        (∀ β, A.Legal β → A.Pure β → A.decomposition.Pure (A.profileInverse β)) := by sorry

end CorrelatedAuctionComplexity.Main
